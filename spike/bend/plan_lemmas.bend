# `diff` over the folder believes the digest a statement gives a file of
# lines. It replays at the position exactly the files of lines whose digest
# no statement settles, and reads from the folder exactly the regular files
# nothing at the position settles: a path the position lacks, or holds as a
# file of lines whose stated digest is not the folder's.
import Base
import ./text.bend as T
import ./tree.bend as Tree
import ./folder.bend as Folder
import ./store.bend as Store
import ./revision.bend as Rev
import ./commands.bend as Main

def keep2(-b1: Bool, -b2: Bool, -x: String, -l1: List<&2, String>, -l2: List<&2, String>, eb: {b1 == b2 : Bool}, el: {l1 == l2 : List<&2, String>}) -> {Rev.keep(b1, x, l1) == Rev.keep(b2, x, l2) : List<&2, String>}:
  %eb : {Rev.keep(b1, x, l1) == Rev.keep(_, x, l2) : List<&2, String>}
  %el : {Rev.keep(b1, x, l1) == Rev.keep(b1, x, _) : List<&2, String>}
  {==}

# One path: whatever the position and the folder hold there, the plan
# replays it where it is a file of lines no statement settles, and reads it
# where the folder holds a regular file nothing at the position settles.
def replay_flag(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, h: Main.Here) -> {Bool.and(Main.here.lines(h), Bool.not(Bool.and(Main.here.regular(h), Main.here.same(eds, os, h, Main.here.digest(dg, h))))) == Bool.and(Main.here.lines(h), Bool.not(Main.here.settled(dg, os, eds, h))) : Bool}:
  match h:
    case Main.Here{p, None{}, found}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, None{}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.Link{r, x}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, found}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, found}:
      {==}

def read_flag(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, h: Main.Here) -> {Bool.and(Main.here.regular(h), Bool.or(Bool.not(Main.here.held(h)), Bool.and(Main.here.lines(h), Bool.not(Main.here.same(eds, os, h, Main.here.digest(dg, h)))))) == Bool.and(Main.here.regular(h), Bool.not(Bool.or(Main.here.kept(h), Main.here.settled(dg, os, eds, h)))) : Bool}:
  match h:
    case Main.Here{p, e, None{}}:
      {==}
    case Main.Here{p, e, Some{Folder.Found.Link{r, x}}}:
      {==}
    case Main.Here{p, None{}, Some{Folder.Found.File{r, x, n}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Lines{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Whole{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      {==}
    case Main.Here{p, Some{Tree.Entry{f, q, Tree.Link{}, y, g, m}}, Some{Folder.Found.File{r, x, n}}}:
      {==}

# `diff` over the folder replays exactly the files of lines no statement
# settles.
def replayed_unsettled(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, hs: List<&2, Main.Here>) -> {Main.planned.replayed(Main.plans(dg, os, eds, hs)) == Main.unsettled.files(dg, os, eds, hs) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      keep2(Bool.and(Main.here.lines(h), Bool.not(Bool.and(Main.here.regular(h), Main.here.same(eds, os, h, Main.here.digest(dg, h))))), Bool.and(Main.here.lines(h), Bool.not(Main.here.settled(dg, os, eds, h))), Main.here.file(h),
        Main.planned.replayed(Main.plans(dg, os, eds, rest)), Main.unsettled.files(dg, os, eds, rest),
        replay_flag(dg, os, eds, h), replayed_unsettled(dg, os, eds, rest))

# And reads exactly the regular files nothing at the position settles.
def read_unsettled(+dg: Map<&2, String>, +os: Map<&2, T.Split>, +eds: List<&2, Store.Doc>, hs: List<&2, Main.Here>) -> {Main.planned.read(Main.plans(dg, os, eds, hs)) == Main.unsettled.paths(dg, os, eds, hs) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      keep2(Bool.and(Main.here.regular(h), Bool.or(Bool.not(Main.here.held(h)), Bool.and(Main.here.lines(h), Bool.not(Main.here.same(eds, os, h, Main.here.digest(dg, h)))))), Bool.and(Main.here.regular(h), Bool.not(Bool.or(Main.here.kept(h), Main.here.settled(dg, os, eds, h)))), Main.here.path(h),
        Main.planned.read(Main.plans(dg, os, eds, rest)), Main.unsettled.paths(dg, os, eds, rest),
        read_flag(dg, os, eds, h), read_unsettled(dg, os, eds, rest))
