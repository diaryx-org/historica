//! Change sets, decision 0090: a line proposed beside a history, under shared
//! bookmarks, and decided by a merge or a tombstone.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use historica::change_set::{
    self, ChangeSetError, Declining, Part, Proposing, Reconciled, State, fact_name, tip_name,
};
use historica::core::{ChangeState, RevisionId};
use historica::record::{Clock as _, Platform, Recorded, Recording, Restriction, record};
use historica::store::{Bookmark, Name, ReceiveError, Store};
use historica::working::Working;

const PERSON: &str = "Adam Harris <adam@example.com>";
const AGENT: &str = "agent:claude-opus-5-5";

fn scratch(test: &str) -> PathBuf {
    let path = Path::new(env!("CARGO_TARGET_TMPDIR")).join(test);
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(&path).expect("a scratch directory");
    path
}

fn record_folder(
    store: &mut Store,
    base: &Path,
    parents: Vec<RevisionId>,
    message: &str,
    author: &str,
) -> Recorded {
    let mut platform = Platform;
    let working = Working::read(base, store.skipped()).expect("the folder");
    record(
        store,
        &working,
        &Recording {
            parents,
            author: author.to_owned(),
            when: platform.now().expect("a clock"),
            message: message.to_owned(),
            moves: Vec::new(),
            at: Vec::new(),
            accepted: BTreeSet::new(),
            only: Restriction::Everything,
            kinds: Default::default(),
            extensions: Default::default(),
        },
        &mut platform,
    )
    .expect("recording")
}

fn proposing(on: RevisionId, message: &str) -> Proposing {
    Proposing {
        on: vec![on],
        author: AGENT.to_owned(),
        when: Platform.now().expect("a clock"),
        message: message.to_owned(),
        extensions: [("diaryx.by".to_owned(), "thread-1".to_owned())].into(),
    }
}

fn declining(message: &str) -> Declining {
    Declining {
        author: PERSON.to_owned(),
        when: Platform.now().expect("a clock"),
        message: message.to_owned(),
    }
}

/// A library with one revision of the person's, and the folder it was
/// recorded from.
fn library(test: &str) -> (PathBuf, Store, RevisionId) {
    let base = scratch(test);
    let mut store = Store::init(base.join("history")).expect("a new store");
    fs::write(base.join("notes.md"), "First thought.\n").expect("a file");
    let first = record_folder(&mut store, &base, Vec::new(), "Start a journal", PERSON);
    (base, store, first.revision)
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("a directory");
    for entry in fs::read_dir(from).expect("a directory") {
        let entry = entry.expect("an entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("a type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), target).expect("a copy");
        }
    }
}

#[test]
fn proposing_writes_an_opening_that_records_nothing_and_pins_it() {
    let (_base, mut store, head) = library("change-set-propose");
    let proposed = change_set::propose(
        &mut store,
        &proposing(head, "Tidy the reading list\n\nThree pages, one list."),
        &mut Platform,
    )
    .expect("proposing");

    assert_eq!(proposed.title, "Tidy the reading list");
    assert_eq!(proposed.description, "Three pages, one list.");
    assert_eq!(proposed.author, AGENT);
    assert_eq!(proposed.base, BTreeSet::from([head]));
    assert_eq!(proposed.tip, proposed.opening);
    assert!(proposed.steps.is_empty());
    assert_eq!(proposed.state(), State::Open);

    // The identity is the opening's change, and the bookmark is shared and
    // pins the opening.
    let opening = store.get(&proposed.opening).unwrap().unwrap();
    assert_eq!(opening.change, proposed.id);
    assert!(opening.added.is_empty() && opening.edited.is_empty());
    assert_eq!(opening.extensions["diaryx.by"], "thread-1");
    assert_eq!(
        store.bookmark(&tip_name(&proposed.id)),
        Some(Bookmark::shared(Name::Revision(proposed.opening)))
    );
    // Its content is the base's: nothing is recorded.
    let file = *store.tree(&head).unwrap().files().next().unwrap().0;
    assert_eq!(
        store.content(&proposed.opening, &file).unwrap().text(),
        store.content(&head, &file).unwrap().text()
    );
    assert!(Store::check(store.root()).is_ok());

    let listed = store.change_sets().expect("listing");
    assert_eq!(listed, vec![proposed]);
}

#[test]
fn a_proposal_wants_a_title_and_a_base_this_store_holds() {
    let (_base, mut store, head) = library("change-set-propose-refusals");
    assert!(matches!(
        change_set::propose(&mut store, &proposing(head, "  \n"), &mut Platform),
        Err(ChangeSetError::NoTitle)
    ));
    let mut elsewhere = proposing(head, "Title");
    elsewhere.on = vec![RevisionId::from_bytes([7; 32])];
    assert!(matches!(
        change_set::propose(&mut store, &elsewhere, &mut Platform),
        Err(ChangeSetError::NotHeld { .. })
    ));
    let mut header = proposing(head, "Title");
    header.extensions = [("by".to_owned(), "x".to_owned())].into();
    assert!(matches!(
        change_set::propose(&mut store, &header, &mut Platform),
        Err(ChangeSetError::UnusableHeader { .. })
    ));
    assert!(store.change_sets().unwrap().is_empty());
}

#[test]
fn recording_onto_the_tip_is_the_next_step_and_recording_elsewhere_is_not() {
    let (base, mut store, head) = library("change-set-steps");
    let proposed = change_set::propose(&mut store, &proposing(head, "Add a line"), &mut Platform)
        .expect("proposing");

    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let one = record_folder(&mut store, &base, vec![proposed.tip], "Add a second", AGENT);
    assert!(one.advanced.contains(&tip_name(&proposed.id)));
    fs::write(
        base.join("notes.md"),
        "First thought.\nA second.\nA third.\n",
    )
    .unwrap();
    let two = record_folder(&mut store, &base, vec![one.revision], "Add a third", AGENT);

    let read = store.change_set(&proposed.id).unwrap();
    assert_eq!(read.tip, two.revision);
    assert_eq!(read.steps, vec![one.revision, two.revision]);

    // The person recording on their own head does not touch it.
    fs::write(base.join("other.md"), "Elsewhere.\n").unwrap();
    let mine = record_folder(&mut store, &base, vec![head], "Mine", PERSON);
    assert!(!mine.advanced.contains(&tip_name(&proposed.id)));
    assert_eq!(store.change_set(&proposed.id).unwrap().tip, two.revision);

    // Advancing by hand wants a revision further along the line.
    assert!(matches!(
        change_set::advance(&mut store, &proposed.id, mine.revision),
        Err(ChangeSetError::NotForward { .. })
    ));
}

#[test]
fn submitting_pins_the_tip_and_an_empty_change_set_has_nothing_to_submit() {
    let (base, mut store, head) = library("change-set-submit");
    let proposed = change_set::propose(&mut store, &proposing(head, "Add a line"), &mut Platform)
        .expect("proposing");
    assert!(matches!(
        change_set::submit(&mut store, &proposed.id),
        Err(ChangeSetError::Empty { .. })
    ));

    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let step = record_folder(&mut store, &base, vec![proposed.tip], "Add a second", AGENT);
    let submitted = change_set::submit(&mut store, &proposed.id).expect("submitting");
    assert_eq!(submitted.state(), State::Submitted);
    assert_eq!(submitted.submitted, Some(step.revision));
    assert_eq!(
        store.name(&fact_name(&proposed.id, change_set::SUBMITTED)),
        Some(Name::Revision(step.revision))
    );
}

#[test]
fn accepting_is_a_merge_naming_the_tip_and_the_merge_leaves_the_tip_where_it_was() {
    let (base, mut store, head) = library("change-set-accept");
    let proposed = change_set::propose(&mut store, &proposing(head, "Add a line"), &mut Platform)
        .expect("proposing");
    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let step = record_folder(&mut store, &base, vec![proposed.tip], "Add a second", AGENT);

    // A revision on the tip with one parent is a step, not an acceptance.
    fs::write(base.join("notes.md"), "First thought.\nA second.\nMore.\n").unwrap();
    let more = record_folder(&mut store, &base, vec![step.revision], "More", AGENT);
    assert!(matches!(
        change_set::accept(&mut store, &proposed.id, more.revision),
        Err(ChangeSetError::NotAMerge { .. })
    ));

    // Nothing moved on the person's side, so the merge joins the line to its
    // own base: the folder is the tip's, and the merge says the line is in.
    let merge = record_folder(
        &mut store,
        &base,
        vec![head, more.revision],
        "Accept \"Add a line\"",
        PERSON,
    );
    assert!(!merge.advanced.contains(&tip_name(&proposed.id)));
    assert_eq!(
        store.acceptances(&proposed.id).unwrap(),
        vec![merge.revision]
    );
    let accepted = change_set::accept(&mut store, &proposed.id, merge.revision).expect("accepting");
    assert_eq!(accepted.state(), State::Accepted);
    assert_eq!(accepted.tip, more.revision);
    assert_eq!(accepted.accepted, Some(merge.revision));

    // Decided is decided.
    assert!(matches!(
        change_set::decline(&mut store, &proposed.id, &declining("no"), &mut Platform),
        Err(ChangeSetError::Decided {
            state: State::Accepted,
            ..
        })
    ));
    // And a step recorded on the old tip afterwards is not the change set's.
    fs::write(base.join("notes.md"), "Late.\n").unwrap();
    let late = record_folder(&mut store, &base, vec![more.revision], "Late", AGENT);
    assert!(!late.advanced.contains(&tip_name(&proposed.id)));
    assert!(Store::check(store.root()).is_ok());
}

#[test]
fn declining_abandons_the_line_with_one_tombstone_and_pins_it() {
    let (base, mut store, head) = library("change-set-decline");
    let proposed = change_set::propose(&mut store, &proposing(head, "Add a line"), &mut Platform)
        .expect("proposing");
    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let step = record_folder(&mut store, &base, vec![proposed.tip], "Add a second", AGENT);

    assert!(matches!(
        change_set::decline(&mut store, &proposed.id, &declining(" "), &mut Platform),
        Err(ChangeSetError::Record(_))
    ));
    let declined = change_set::decline(
        &mut store,
        &proposed.id,
        &declining("Declined \"Add a line\": not this week"),
        &mut Platform,
    )
    .expect("declining");
    assert_eq!(declined.state(), State::Declined);
    let tombstone = declined.declined.expect("the tombstone");

    // Decision 0013: the change set's change is abandoned, the tombstone
    // stands on the base, and the tip pin stays on the work it pinned.
    let history = store.history();
    assert!(matches!(
        history.change_state(&proposed.id),
        ChangeState::Abandoned
    ));
    let document = store.get(&tombstone).unwrap().unwrap();
    assert_eq!(document.parents, BTreeSet::from([head]));
    assert_eq!(
        document.supersedes,
        BTreeSet::from([proposed.opening, step.revision])
    );
    assert_eq!(declined.tip, step.revision);
    assert_eq!(declined.title, "Add a line");

    // Declined is decided.
    assert!(matches!(
        change_set::submit(&mut store, &proposed.id),
        Err(ChangeSetError::Decided { .. })
    ));
    assert!(Store::check(store.root()).is_ok());
}

#[test]
fn a_receive_takes_the_tip_further_along_and_refuses_two_that_part() {
    let (base, mut store, head) = library("change-set-receive");
    let proposed = change_set::propose(&mut store, &proposing(head, "Add a line"), &mut Platform)
        .expect("proposing");

    // The phone has the change set as it was proposed.
    let phone_dir = scratch("change-set-receive-phone");
    copy_dir(&base.join("history"), &phone_dir.join("history"));
    let mut phone = Store::open(phone_dir.join("history")).expect("the phone's store");

    // The laptop adds a step and submits.
    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let step = record_folder(&mut store, &base, vec![proposed.tip], "Add a second", AGENT);
    change_set::submit(&mut store, &proposed.id).expect("submitting");

    // The phone takes the tip forward and learns of the submission.
    phone.receive(&store, false).expect("receiving");
    let there = phone.change_set(&proposed.id).unwrap();
    assert_eq!(there.tip, step.revision);
    assert_eq!(there.state(), State::Submitted);

    // The laptop, behind nothing, keeps its own.
    store.receive(&phone, false).expect("receiving back");
    assert_eq!(store.change_set(&proposed.id).unwrap().tip, step.revision);

    // The phone declines; the laptop hears of it.
    change_set::decline(&mut phone, &proposed.id, &declining("No"), &mut Platform)
        .expect("declining");
    store
        .receive(&phone, false)
        .expect("receiving the decision");
    assert_eq!(
        store.change_set(&proposed.id).unwrap().state(),
        State::Declined
    );

    // Two tips on two lines are a conflict, as any bookmark is.
    let other = change_set::propose(&mut store, &proposing(head, "Another"), &mut Platform)
        .expect("proposing");
    phone
        .receive(&store, false)
        .expect("receiving the proposal");
    fs::write(base.join("notes.md"), "Left.\n").unwrap();
    record_folder(&mut store, &base, vec![other.tip], "Left", AGENT);
    let phone_folder = phone_dir.clone();
    fs::write(phone_folder.join("notes.md"), "Right.\n").unwrap();
    record_folder(&mut phone, &phone_folder, vec![other.tip], "Right", AGENT);
    assert!(matches!(
        phone.receive(&store, false),
        Err(ReceiveError::Mutable { .. })
    ));
}

#[test]
fn decided_both_ways_reads_as_accepted_and_keeps_the_tombstone() {
    let (base, mut store, head) = library("change-set-both-ways");
    let proposed = change_set::propose(&mut store, &proposing(head, "Add a line"), &mut Platform)
        .expect("proposing");
    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let step = record_folder(&mut store, &base, vec![proposed.tip], "Add a second", AGENT);

    let phone_dir = scratch("change-set-both-ways-phone");
    copy_dir(&base.join("history"), &phone_dir.join("history"));
    let mut phone = Store::open(phone_dir.join("history")).expect("the phone's store");
    change_set::decline(&mut phone, &proposed.id, &declining("No"), &mut Platform)
        .expect("declining on the phone");

    let merge = record_folder(
        &mut store,
        &base,
        vec![head, step.revision],
        "Accept",
        PERSON,
    );
    change_set::accept(&mut store, &proposed.id, merge.revision).expect("accepting");

    store.receive(&phone, false).expect("receiving");
    let read = store.change_set(&proposed.id).unwrap();
    assert_eq!(read.state(), State::Accepted);
    assert!(read.declined.is_some());
}

#[test]
fn reconciling_moves_only_a_change_sets_moving_parts_forward() {
    let (base, mut store, head) = library("change-set-reconcile");
    let proposed = change_set::propose(&mut store, &proposing(head, "Add a line"), &mut Platform)
        .expect("proposing");
    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let step = record_folder(&mut store, &base, vec![proposed.tip], "Add a second", AGENT);
    let history = store.history();
    let at = |revision| Bookmark::shared(Name::Revision(revision));

    let tip = tip_name(&proposed.id);
    assert_eq!(
        change_set::reconcile(&history, &tip, at(proposed.opening), at(step.revision)),
        Reconciled::Take(at(step.revision))
    );
    assert_eq!(
        change_set::reconcile(&history, &tip, at(step.revision), at(proposed.opening)),
        Reconciled::Keep
    );
    // A private reading joins, as decision 0062 has it.
    assert_eq!(
        change_set::reconcile(
            &history,
            &tip,
            at(step.revision),
            Bookmark::private(Name::Revision(proposed.opening))
        ),
        Reconciled::Take(Bookmark::private(Name::Revision(step.revision)))
    );
    // An acceptance is written once, and any other pin is a pin.
    let accepted = fact_name(&proposed.id, change_set::ACCEPTED);
    for name in [accepted.as_str(), "main"] {
        assert_eq!(
            change_set::reconcile(&history, name, at(proposed.opening), at(step.revision)),
            Reconciled::Conflict
        );
    }

    assert_eq!(Part::of(&tip), Some(Part::Tip(proposed.id)));
    assert_eq!(Part::of(&accepted), Some(Part::Accepted(proposed.id)));
    assert_eq!(Part::of("change-sets/not-an-id"), None);
    assert_eq!(Part::of(&format!("{tip}/other")), None);
    assert_eq!(Part::of("main"), None);
}

/// A store copied whole, as a second replica.
fn replica(store: &Store, test: &str) -> (PathBuf, Store) {
    let dir = scratch(test);
    copy_dir(store.root(), &dir.join("history"));
    let copy = Store::open(dir.join("history")).expect("the copy");
    (dir, copy)
}

#[test]
fn a_step_recorded_before_hearing_of_an_acceptance_is_not_accepted() {
    for accepting_side_receives in [true, false] {
        let test = format!("change-set-accept-race-{accepting_side_receives}");
        let (base, mut laptop, head) = library(&test);
        let proposed =
            change_set::propose(&mut laptop, &proposing(head, "Add a line"), &mut Platform)
                .expect("proposing");
        fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
        let step = record_folder(&mut laptop, &base, vec![proposed.tip], "Second", AGENT);
        let (phone_dir, mut phone) = replica(&laptop, &format!("{test}-phone"));

        // The laptop accepts at the step; the phone, not having heard, adds
        // another.
        let merge = record_folder(
            &mut laptop,
            &base,
            vec![head, step.revision],
            "Accept",
            PERSON,
        );
        change_set::accept(&mut laptop, &proposed.id, merge.revision).expect("accepting");
        fs::write(
            phone_dir.join("notes.md"),
            "First thought.\nA second.\nLate.\n",
        )
        .unwrap();
        let late = record_folder(&mut phone, &phone_dir, vec![step.revision], "Late", AGENT);

        let read = if accepting_side_receives {
            laptop.receive(&phone, false).expect("receiving");
            laptop.change_set(&proposed.id).unwrap()
        } else {
            phone.receive(&laptop, false).expect("receiving");
            phone.change_set(&proposed.id).unwrap()
        };
        assert_eq!(read.state(), State::Accepted);
        assert_eq!(read.tip, step.revision, "the tip is what the merge holds");
        assert_eq!(read.steps, vec![step.revision]);
        assert_eq!(read.after, vec![late.revision]);
    }
}

#[test]
fn a_step_recorded_before_hearing_of_a_decline_is_not_declined() {
    let (base, mut laptop, head) = library("change-set-decline-race");
    let proposed = change_set::propose(&mut laptop, &proposing(head, "Add a line"), &mut Platform)
        .expect("proposing");
    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let step = record_folder(&mut laptop, &base, vec![proposed.tip], "Second", AGENT);
    let (phone_dir, mut phone) = replica(&laptop, "change-set-decline-race-phone");

    change_set::decline(&mut laptop, &proposed.id, &declining("No"), &mut Platform)
        .expect("declining");
    fs::write(phone_dir.join("notes.md"), "Late.\n").unwrap();
    let late = record_folder(&mut phone, &phone_dir, vec![step.revision], "Late", AGENT);

    laptop.receive(&phone, false).expect("receiving");
    let read = laptop.change_set(&proposed.id).unwrap();
    assert_eq!(read.state(), State::Declined);
    assert_eq!(read.tip, step.revision);
    assert_eq!(read.after, vec![late.revision]);
}

#[test]
fn declining_one_change_set_leaves_another_proposed_on_its_tip() {
    let (base, mut store, head) = library("change-set-decline-dependent");
    let first = change_set::propose(&mut store, &proposing(head, "First"), &mut Platform)
        .expect("proposing");
    fs::write(base.join("notes.md"), "First thought.\nA second.\n").unwrap();
    let step = record_folder(&mut store, &base, vec![first.tip], "Second", AGENT);
    let second = change_set::propose(
        &mut store,
        &proposing(step.revision, "Second"),
        &mut Platform,
    )
    .expect("proposing on the first's tip");

    match change_set::decline(&mut store, &first.id, &declining("No"), &mut Platform) {
        Err(ChangeSetError::StoodOn { revisions, .. }) => {
            assert_eq!(revisions, vec![second.opening]);
        }
        other => panic!("declined over another change set: {other:?}"),
    }
    let history = store.history();
    assert!(matches!(
        history.change_state(&second.id),
        ChangeState::Resolved(_)
    ));
    assert_eq!(store.change_set(&first.id).unwrap().state(), State::Open);

    // Declining the one on top first leaves the first free to go.
    change_set::decline(&mut store, &second.id, &declining("No"), &mut Platform)
        .expect("declining the second");
    let declined = change_set::decline(&mut store, &first.id, &declining("No"), &mut Platform)
        .expect("declining the first");
    let tombstone = store.get(&declined.declined.unwrap()).unwrap().unwrap();
    assert_eq!(
        tombstone.supersedes,
        BTreeSet::from([first.opening, step.revision])
    );
    assert!(Store::check(store.root()).is_ok());
}

#[test]
fn a_retitled_change_set_declines_and_keeps_its_new_title() {
    use historica::record::{Amendment, amend};

    let (base, mut store, head) = library("change-set-decline-retitled");
    let proposed = change_set::propose(&mut store, &proposing(head, "First title"), &mut Platform)
        .expect("proposing");
    let working = Working::read(&base, store.skipped()).expect("the folder");
    let amended = amend(
        &mut store,
        &working,
        &Amendment {
            revision: proposed.opening,
            message: Some("Retitled".to_owned()),
            reviser: AGENT.to_owned(),
            revised: Platform.now().unwrap(),
            moves: Vec::new(),
        },
        &mut Platform,
    )
    .expect("retitling");
    assert_eq!(store.change_set(&proposed.id).unwrap().title, "Retitled");

    let declined = change_set::decline(&mut store, &proposed.id, &declining("No"), &mut Platform)
        .expect("declining a retitled change set");
    assert_eq!(declined.state(), State::Declined);
    assert_eq!(declined.title, "Retitled");
    let tombstone = store.get(&declined.declined.unwrap()).unwrap().unwrap();
    assert_eq!(tombstone.supersedes, BTreeSet::from([amended.revision]));
    assert!(matches!(
        store.history().change_state(&proposed.id),
        ChangeState::Abandoned
    ));
    assert!(Store::check(store.root()).is_ok());
}
