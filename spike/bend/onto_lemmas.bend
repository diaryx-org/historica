# What `export` promises of a copy's store it brings up to date. It writes
# only into a copy related to this store holding nothing this store has
# not heard of.
import Base
import ./export.bend as Export
import ./receive.bend as Receive
import ./receive_lemmas.bend as ReceiveL
import ./catchup_lemmas.bend as CatchL
import ./export_lemmas.bend as ExportL
import ./commands.bend as Main
import ./revision.bend as Rev
import ./text.bend as T
import ./sort_lemmas.bend as SortL
import ./anchor_lemmas.bend as AL
import ./arrange.bend as Arrange

# Which copy an export writes into
# --------------------------------

# What a copy's revision is found among: the digests this store holds and
# those its revisions name.
def edges_named(fs: List<&2, Main.Full>, +id: String) -> {Rev.member(Export.named.edges(fs), id) == Export.named.edge(fs, id) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Main.Full{i, c, +parents, +supersedes, a, w, rb, rv, facts, m} <> +rest:
      %Equal.sym(Bool, Rev.member(List.append(&2, String, parents, List.append(&2, String, supersedes, List.append(&2, String, Export.named.edges(rest), Nil{}))), id), Bool.or(Rev.member(parents, id), Rev.member(List.append(&2, String, supersedes, List.append(&2, String, Export.named.edges(rest), Nil{})), id)), ReceiveL.member_app(parents, List.append(&2, String, supersedes, List.append(&2, String, Export.named.edges(rest), Nil{})), id)) : {_ == Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Export.named.edge(rest, id)) : Bool}
      %Equal.sym(Bool, Rev.member(List.append(&2, String, supersedes, List.append(&2, String, Export.named.edges(rest), Nil{})), id), Bool.or(Rev.member(supersedes, id), Rev.member(List.append(&2, String, Export.named.edges(rest), Nil{}), id)), ReceiveL.member_app(supersedes, List.append(&2, String, Export.named.edges(rest), Nil{}), id)) : {Bool.or(Rev.member(parents, id), _) == Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Export.named.edge(rest, id)) : Bool}
      %Equal.sym(List<&2, String>, List.append(&2, String, Export.named.edges(rest), Nil{}), Export.named.edges(rest), SortL.lapp_nil(String, Export.named.edges(rest))) : {Bool.or(Rev.member(parents, id), Bool.or(Rev.member(supersedes, id), Rev.member(_, id))) == Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Export.named.edge(rest, id)) : Bool}
      %Equal.sym(Bool, Rev.member(Export.named.edges(rest), id), Export.named.edge(rest, id), edges_named(rest, id)) : {Bool.or(Rev.member(parents, id), Bool.or(Rev.member(supersedes, id), _)) == Bool.or(Bool.or(Rev.member(parents, id), Rev.member(supersedes, id)), Export.named.edge(rest, id)) : Bool}
      ReceiveL.or_assoc(Rev.member(parents, id), Rev.member(supersedes, id), Export.named.edge(rest, id))

def heard_is(+fs: List<&2, Main.Full>, +id: String) -> {Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), id) == Bool.or(Rev.member(Main.ids(fs), id), Export.named.edge(fs, id)) : Bool}:
  Equal.trans(Bool, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), id), Rev.member(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)), id), Bool.or(Rev.member(Main.ids(fs), id), Export.named.edge(fs, id)),
    CatchL.has_member(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)), id),
    Equal.trans(Bool, Rev.member(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)), id), Bool.or(Rev.member(Main.ids(fs), id), Rev.member(Export.named.edges(fs), id)), Bool.or(Rev.member(Main.ids(fs), id), Export.named.edge(fs, id)),
      ReceiveL.member_app(Main.ids(fs), Export.named.edges(fs), id),
      Equal.cong(Bool, Bool, x => Bool.or(Rev.member(Main.ids(fs), id), x), Rev.member(Export.named.edges(fs), id), Export.named.edge(fs, id), edges_named(fs, id))))

def stranger_step(c: Bool, +f: Main.Full, +rest: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +into: String, ec: {Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)) == c : Bool}, ih: {Result.is_done(&2, &2, Main.Refused, Unit, Export.stranger.r(into, Export.stranger(rest, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)))))) == Export.heard.all(rest, fs) : Bool}) -> {Result.is_done(&2, &2, Main.Refused, Unit, Export.stranger.r(into, Bool.pick(Maybe<&2, String>, c, Export.stranger(rest, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)))), Some{Main.id_of(f)}))) == Bool.and(Bool.or(Rev.member(Main.ids(fs), Main.id_of(f)), Export.named.edge(fs, Main.id_of(f))), Export.heard.all(rest, fs)) : Bool}:
  match c:
    case True{}:
      %Equal.trans(Bool, True{}, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), Bool.or(Rev.member(Main.ids(fs), Main.id_of(f)), Export.named.edge(fs, Main.id_of(f))), Equal.sym(Bool, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), True{}, ec), heard_is(fs, Main.id_of(f))) : {Result.is_done(&2, &2, Main.Refused, Unit, Export.stranger.r(into, Export.stranger(rest, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)))))) == Bool.and(_, Export.heard.all(rest, fs)) : Bool}
      ih
    case False{}:
      %Equal.trans(Bool, False{}, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), Bool.or(Rev.member(Main.ids(fs), Main.id_of(f)), Export.named.edge(fs, Main.id_of(f))), Equal.sym(Bool, Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), False{}, ec), heard_is(fs, Main.id_of(f))) : {False{} == Bool.and(_, Export.heard.all(rest, fs)) : Bool}
      {==}

# The copy holds no revision this store has not heard of exactly where no
# stranger is found in it.
def stranger_done(cfs: List<&2, Main.Full>, +fs: List<&2, Main.Full>, +into: String) -> {Result.is_done(&2, &2, Main.Refused, Unit, Export.stranger.r(into, Export.stranger(cfs, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs)))))) == Export.heard.all(cfs, fs) : Bool}:
  match cfs:
    case Nil{}:
      {==}
    case +f <> +rest:
      stranger_step(Arrange.has(Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))), Main.id_of(f)), f, rest, fs, into, {==}, stranger_done(rest, fs, into))

def rel_step(b: Bool, +into: String, +fs: List<&2, Main.Full>, +cfs: List<&2, Main.Full>) -> {Result.is_done(&2, &2, Main.Refused, Unit, Result.bind(&2, &2, Main.Refused, Unit, Unit, Bool.pick(Result<&2, &2, Main.Refused, Unit>, b, Done{Unit{}}, Fail{Main.Refused{1, Export.UNRELATED(into)}}), u => Export.stranger.r(into, Export.stranger(cfs, Set.from_list(List.append(&2, String, Main.ids(fs), Export.named.edges(fs))))))) == Bool.and(b, Export.heard.all(cfs, fs)) : Bool}:
  match b:
    case True{}:
      stranger_done(cfs, fs, into)
    case False{}:
      {==}

# An export writes into a copy exactly where the copy is related to this
# store and holds no revision this store has not heard of.
def copy_done(+into: String, +fs: List<&2, Main.Full>, +cfs: List<&2, Main.Full>) -> {Result.is_done(&2, &2, Main.Refused, Unit, Export.copy.r(into, fs, cfs)) == Bool.and(Receive.related(fs, cfs), Export.heard.all(cfs, fs)) : Bool}:
  rel_step(Receive.related(fs, cfs), into, fs, cfs)
