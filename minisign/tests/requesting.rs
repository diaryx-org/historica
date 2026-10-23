//! A request signed by a device key, checked as a server checks one.
//!
//! Every refusal here is one a hub must make: a header from a key it was not
//! given, one moved to another path or method, one too old or too far ahead,
//! and one that is not the grammar at all.

#![cfg(feature = "sign")]

use historica_minisign::Key;
use historica_minisign::key::mint;
use historica_minisign::request::{
    DEFAULT_MAX_SKEW, KeyId, Refusal, TOKEN_PATH, Target, sign_request, verify_request,
};
use historica_minisign::sign::{SecretKey, public_key};

const HOST: &str = "hub.example.org";
const PATH: &str = "/adam/notes/offer.txt";
const NOW: u64 = 1_760_968_324;

fn keys() -> (SecretKey, Key) {
    let secret = mint().expect("a key");
    let key = public_key(&secret).expect("its public half");
    (secret, key)
}

/// A server that holds `held` and nothing else.
fn holding(held: &Key) -> impl FnOnce(&KeyId) -> Option<Key> + '_ {
    move |id| (*id == held.id()).then(|| held.clone())
}

fn check(header: &str, method: &str, path: &str, now: u64, held: &Key) -> Result<KeyId, Refusal> {
    verify_request(
        header,
        method,
        HOST,
        path,
        now,
        DEFAULT_MAX_SKEW,
        holding(held),
    )
}

#[test]
fn a_signed_request_verifies_and_names_its_key() {
    let (secret, key) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");

    let mut fields = header.split(' ');
    assert_eq!(fields.next(), Some("Minisign"));
    assert_eq!(fields.next(), Some(key.id().to_string().as_str()));
    assert_eq!(fields.next(), Some("1760968324"));
    assert_eq!(fields.next().map(str::len), Some(184));
    assert_eq!(fields.next(), None);

    assert_eq!(check(&header, "GET", PATH, NOW, &key), Ok(key.id()));
    // Anywhere inside the window, either way.
    assert!(check(&header, "GET", PATH, NOW + DEFAULT_MAX_SKEW, &key).is_ok());
    assert!(check(&header, "GET", PATH, NOW - DEFAULT_MAX_SKEW, &key).is_ok());
    // HTTP says a scheme is case-insensitive, so a server takes it so.
    let lower = header.replacen("Minisign", "minisign", 1);
    assert!(check(&lower, "GET", PATH, NOW, &key).is_ok());
}

#[test]
fn the_token_request_is_signed_over_its_method_and_path() {
    let (secret, key) = keys();
    let hub = Target::of("https://Hub.Example.org/").expect("a hub");
    let header = sign_request(&secret, "POST", &hub.host, TOKEN_PATH, NOW).expect("a header");
    assert!(check(&header, "POST", TOKEN_PATH, NOW, &key).is_ok());
    assert!(check(&header, "GET", TOKEN_PATH, NOW, &key).is_err());
}

#[test]
fn a_key_the_server_does_not_hold_is_refused() {
    let (secret, key) = keys();
    let (_, other) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    assert_eq!(
        check(&header, "GET", PATH, NOW, &other),
        Err(Refusal::UnknownKey { key: key.id() })
    );
}

#[test]
fn a_lookup_that_answers_with_another_key_is_refused() {
    let (secret, key) = keys();
    let (_, other) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    let refused = verify_request(&header, "GET", HOST, PATH, NOW, DEFAULT_MAX_SKEW, |_| {
        Some(other.clone())
    });
    assert_eq!(
        refused,
        Err(Refusal::WrongKey {
            asked: key.id(),
            found: other.id()
        })
    );
}

#[test]
fn a_header_naming_a_key_that_did_not_sign_it_is_refused() {
    // Somebody else's key ID on this signature: the ID is not trusted, and
    // the signature carries the ID of the key that made it.
    let (secret, _) = keys();
    let (_, other) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    let fields: Vec<&str> = header.split(' ').collect();
    let forged = format!("Minisign {} {} {}", other.id(), fields[2], fields[3]);
    assert!(matches!(
        check(&forged, "GET", PATH, NOW, &other),
        Err(Refusal::Malformed { .. })
    ));
}

#[test]
fn a_signature_by_another_key_with_the_same_id_does_not_check() {
    // The worst a lookup can be handed: a key whose ID collides. The signature
    // is what decides, and it was not made by this key.
    let (secret, key) = keys();
    let (other_secret, _) = keys();
    let header = sign_request(&other_secret, "GET", HOST, PATH, NOW).expect("a header");
    let fields: Vec<&str> = header.split(' ').collect();
    let mine = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    let mine: Vec<&str> = mine.split(' ').collect();
    // This key's ID and most of its signature line, the rest from a
    // signature the other key made over the same request.
    let spliced = format!(
        "Minisign {} {} {}{}",
        key.id(),
        fields[2],
        &mine[3][..96],
        &fields[3][96..]
    );
    assert!(check(&spliced, "GET", PATH, NOW, &key).is_err());
}

#[test]
fn a_header_moved_to_another_path_is_refused() {
    let (secret, key) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    for path in [
        "/adam/notes/offer.txt?v=1",
        "/adam/notes/offer.tx",
        "/adam/other/offer.txt",
        "/adam/notes/%6Ffer.txt",
    ] {
        assert!(
            matches!(
                check(&header, "GET", path, NOW, &key),
                Err(Refusal::Signature { .. })
            ),
            "the header read {path}"
        );
    }
    let elsewhere = verify_request(
        &header,
        "GET",
        "evil.example.org",
        PATH,
        NOW,
        DEFAULT_MAX_SKEW,
        holding(&key),
    );
    assert!(matches!(elsewhere, Err(Refusal::Signature { .. })));
}

#[test]
fn a_header_moved_to_another_method_is_refused() {
    let (secret, key) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    for method in ["POST", "HEAD", "DELETE"] {
        assert!(matches!(
            check(&header, method, PATH, NOW, &key),
            Err(Refusal::Signature { .. })
        ));
    }
    assert!(matches!(
        check(&header, "get", PATH, NOW, &key),
        Err(Refusal::Request(_))
    ));
}

#[test]
fn a_header_older_than_the_window_is_refused() {
    let (secret, key) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    let later = NOW + DEFAULT_MAX_SKEW + 1;
    assert_eq!(
        check(&header, "GET", PATH, later, &key),
        Err(Refusal::Stale {
            time: NOW,
            now: later
        })
    );
}

#[test]
fn a_header_further_ahead_than_the_window_is_refused() {
    let (secret, key) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    let earlier = NOW - DEFAULT_MAX_SKEW - 1;
    assert_eq!(
        check(&header, "GET", PATH, earlier, &key),
        Err(Refusal::Future {
            time: NOW,
            now: earlier
        })
    );
}

#[test]
fn a_time_changed_after_signing_is_refused() {
    let (secret, key) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    let moved = header.replacen(&NOW.to_string(), &(NOW + 60).to_string(), 1);
    assert!(matches!(
        check(&moved, "GET", PATH, NOW + 60, &key),
        Err(Refusal::Signature { .. })
    ));
}

#[test]
fn a_malformed_header_is_refused() {
    let (secret, key) = keys();
    let header = sign_request(&secret, "GET", HOST, PATH, NOW).expect("a header");
    let fields: Vec<&str> = header.split(' ').collect();
    let (id, time, signature) = (fields[1], fields[2], fields[3]);
    for malformed in [
        String::new(),
        "Minisign".to_owned(),
        format!("Basic {id} {time} {signature}"),
        format!("Minisign {id} {time}"),
        format!("Minisign {id} {time} {signature} extra"),
        format!("Minisign  {id} {time} {signature}"),
        format!(" Minisign {id} {time} {signature}"),
        format!("Minisign {id} {time} {signature} "),
        format!("Minisign {id}\t{time} {signature}"),
        format!("Minisign {}a {time} {signature}", &id[..15]),
        format!("Minisign {id} 0{time} {signature}"),
        format!("Minisign {id} +{time} {signature}"),
        format!("Minisign {id} {time} {}", &signature[1..]),
        format!("Minisign {id} {time} {signature}="),
        format!("Minisign {id} {time} -{}", &signature[1..]),
        format!("Minisign {id} {time} {}", "A".repeat(184)),
    ] {
        let refused = check(&malformed, "GET", PATH, NOW, &key);
        assert!(
            matches!(refused, Err(Refusal::Malformed { .. })),
            "`{malformed}` was {refused:?}"
        );
    }
}

#[test]
fn a_request_that_cannot_be_written_down_is_not_signed() {
    let (secret, _) = keys();
    for (method, host, path) in [
        ("GET", HOST, "/a\ntime 1"),
        ("GET", "Hub.example.org", PATH),
        ("get", HOST, PATH),
        ("GET", HOST, "offer.txt"),
    ] {
        assert!(sign_request(&secret, method, host, path, NOW).is_err());
    }
}

#[cfg(feature = "http")]
mod source {
    use super::{HOST, check, keys};
    use historica_minisign::http::SignedSource;
    use historica_minisign::request::{Refusal, Target};

    #[test]
    fn every_request_a_fetch_makes_carries_a_header_for_its_own_path() {
        let (secret, key) = keys();
        let source = SignedSource::at(&format!("https://{HOST}/adam/notes/"), secret)
            .expect("a source; nothing is asked of the network to make one");
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("a clock")
            .as_secs();

        let path = source.request_path("history/revisions/2026-08/a second copy.rev.txt");
        assert_eq!(
            path,
            "/adam/notes/history/revisions/2026-08/a%20second%20copy.rev.txt"
        );
        let header = source
            .authorization("history/revisions/2026-08/a second copy.rev.txt")
            .expect("a header");
        assert_eq!(check(&header, "GET", &path, now, &key), Ok(key.id()));
        // And for that path alone.
        assert!(matches!(
            check(&header, "GET", "/adam/notes/offer.txt", now, &key),
            Err(Refusal::Signature { .. })
        ));
        assert_eq!(
            Target::of(&format!("https://{HOST}{path}"))
                .expect("a URL")
                .path,
            path
        );
    }

    #[test]
    fn a_root_that_is_not_a_directory_is_refused() {
        for root in [
            "https://hub.example.org/adam/notes",
            "https://hub.example.org/adam/notes/?v=1",
            "ftp://hub.example.org/adam/notes/",
        ] {
            let (secret, _) = keys();
            assert!(
                SignedSource::at(root, secret).is_err(),
                "`{root}` was taken"
            );
        }
    }
}
