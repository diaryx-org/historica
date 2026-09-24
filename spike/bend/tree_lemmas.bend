# The tree: what `insert` and `remove` do to `lookup`, and what a
# revision `apply` leaves behind.
import Base
import ./tree.bend as T
import ./revision.bend as Rev
import ./string_lemmas.bend as S

# Lookup after insert
# -------------------

# Two files an insert stepped past are not one file.
def gt_self(+f: String, +f2: String, eq: {f2 == f : String}, ec: {String.order(f, f2) == GT{} : Cmp}) -> {String.order(f, f) == GT{} : Cmp}:
  %eq : {String.order(f, _) == GT{} : Cmp}
  ec

def ne_of_gt.of(b: Bool, +f: String, +f2: String, eb: {String.eq(f2, f) == b : Bool}, ec: {String.order(f, f2) == GT{} : Cmp}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.gt_ne(f, gt_self(f, f2, S.eq_true(f2, f, eb), ec)))

def ne_of_gt(+f: String, +f2: String, ec: {String.order(f, f2) == GT{} : Cmp}) -> {String.eq(f2, f) == False{} : Bool}:
  ne_of_gt.of(String.eq(f2, f), f, f2, {==}, ec)

# An entry inserted is the one found under its file...
def lookup_insert.at(c: Cmp, e: T.Entry, first: T.Entry, +rest: T.Tree(), ec: {String.order(T.entry_file(e), T.entry_file(first)) == c : Cmp}, ih: {T.lookup(T.insert(rest, e), T.entry_file(e)) == Some{e} : Maybe<&2, T.Entry>}) -> {T.lookup(T.insert.at(c, e, first, rest, T.insert(rest, e)), T.entry_file(e)) == Some{e} : Maybe<&2, T.Entry>}:
  match c:
    case LT{}:
      match e:
        case T.Entry{+f, p, k, y, g, m}:
          %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p, k, y, g, m}}, T.lookup(first <> rest, f)) == Some{T.Entry{f, p, k, y, g, m}} : Maybe<&2, T.Entry>}
          {==}
    case EQ{}:
      match e:
        case T.Entry{+f, p, k, y, g, m}:
          %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p, k, y, g, m}}, T.lookup(rest, f)) == Some{T.Entry{f, p, k, y, g, m}} : Maybe<&2, T.Entry>}
          {==}
    case GT{}:
      match e first:
        case T.Entry{+f, p, k, y, g, m} T.Entry{+f2, p2, k2, y2, g2, m2}:
          %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.insert(rest, T.Entry{f, p, k, y, g, m}), f), Some{T.Entry{f, p, k, y, g, m}}, ih) : {Bool.pick(Maybe<&2, T.Entry>, String.eq(f2, f), Some{T.Entry{f2, p2, k2, y2, g2, m2}}, _) == Some{T.Entry{f, p, k, y, g, m}} : Maybe<&2, T.Entry>}
          %Equal.sym(Bool, String.eq(f2, f), False{}, ne_of_gt(f, f2, ec)) : {Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f2, p2, k2, y2, g2, m2}}, Some{T.Entry{f, p, k, y, g, m}}) == Some{T.Entry{f, p, k, y, g, m}} : Maybe<&2, T.Entry>}
          {==}

def lookup_insert(t: T.Tree(), +e: T.Entry) -> {T.lookup(T.insert(t, e), T.entry_file(e)) == Some{e} : Maybe<&2, T.Entry>}:
  match t:
    case Nil{}:
      match e:
        case T.Entry{+f, p, k, y, g, m}:
          %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p, k, y, g, m}}, None{}) == Some{T.Entry{f, p, k, y, g, m}} : Maybe<&2, T.Entry>}
          {==}
    case +first <> +rest:
      lookup_insert.at(String.order(T.entry_file(e), T.entry_file(first)), e, first, rest, {==}, lookup_insert(rest, e))

# ...and every other file finds what it found before.
def lookup_other.at(c: Cmp, e: T.Entry, first: T.Entry, +rest: T.Tree(), +x: String, ec: {String.order(T.entry_file(e), T.entry_file(first)) == c : Cmp}, ne: {String.eq(T.entry_file(e), x) == False{} : Bool}, ih: {T.lookup(T.insert(rest, e), x) == T.lookup(rest, x) : Maybe<&2, T.Entry>}) -> {T.lookup(T.insert.at(c, e, first, rest, T.insert(rest, e)), x) == T.lookup(first <> rest, x) : Maybe<&2, T.Entry>}:
  match c:
    case LT{}:
      match e:
        case T.Entry{+f, p, k, y, g, m}:
          %Equal.sym(Bool, String.eq(f, x), False{}, ne) : {Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p, k, y, g, m}}, T.lookup(first <> rest, x)) == T.lookup(first <> rest, x) : Maybe<&2, T.Entry>}
          {==}
    case EQ{}:
      match e first:
        case T.Entry{+f, p, k, y, g, m} T.Entry{+f2, p2, k2, y2, g2, m2}:
          %S.order_eq(f, f2, ec) : {Bool.pick(Maybe<&2, T.Entry>, String.eq(f, x), Some{T.Entry{f, p, k, y, g, m}}, T.lookup(rest, x)) == Bool.pick(Maybe<&2, T.Entry>, String.eq(_, x), Some{T.Entry{_, p2, k2, y2, g2, m2}}, T.lookup(rest, x)) : Maybe<&2, T.Entry>}
          %Equal.sym(Bool, String.eq(f, x), False{}, ne) : {Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p, k, y, g, m}}, T.lookup(rest, x)) == Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p2, k2, y2, g2, m2}}, T.lookup(rest, x)) : Maybe<&2, T.Entry>}
          {==}
    case GT{}:
      match first:
        case T.Entry{+f2, p2, k2, y2, g2, m2}:
          %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.insert(rest, e), x), T.lookup(rest, x), ih) : {Bool.pick(Maybe<&2, T.Entry>, String.eq(f2, x), Some{T.Entry{f2, p2, k2, y2, g2, m2}}, _) == Bool.pick(Maybe<&2, T.Entry>, String.eq(f2, x), Some{T.Entry{f2, p2, k2, y2, g2, m2}}, T.lookup(rest, x)) : Maybe<&2, T.Entry>}
          {==}

def lookup_other(t: T.Tree(), +e: T.Entry, +x: String, +ne: {String.eq(T.entry_file(e), x) == False{} : Bool}) -> {T.lookup(T.insert(t, e), x) == T.lookup(t, x) : Maybe<&2, T.Entry>}:
  match t:
    case Nil{}:
      match e:
        case T.Entry{+f, p, k, y, g, m}:
          %Equal.sym(Bool, String.eq(f, x), False{}, ne) : {Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p, k, y, g, m}}, None{}) == None{} : Maybe<&2, T.Entry>}
          {==}
    case +first <> +rest:
      lookup_other.at(String.order(T.entry_file(e), T.entry_file(first)), e, first, rest, x, {==}, ne, lookup_other(rest, e, x, ne))

# Refutations
# -----------

def donedisc(r: Result<&2, &2, T.Fault, Unit>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{u}:
      Empty

def somedisc(m: Maybe<&2, T.Entry>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{e}:
      Empty

def fail_done(e: T.Fault, d: {Fail{e} == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> Empty:
  %d : {donedisc(_) : Type}
  Unit{}

def treedisc(r: Result<&2, &2, T.Fault, T.Tree()>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{t}:
      Empty

def got(r: Result<&2, &2, T.Fault, T.Tree()>) -> T.Tree():
  match r:
    case Fail{e}:
      Nil{}
    case Done{t}:
      t

def fail_tree(e: T.Fault, t: T.Tree(), d: {Fail{e} == Done{t} : Result<&2, &2, T.Fault, T.Tree()>}) -> Empty:
  %d : {treedisc(_) : Type}
  Unit{}

# One path, one file
# ------------------

# What `path_taken` checks, said of the result: the files at a path are
# at most one, and none where the path is already held.
def fits(xs: List<&2, String>, held: Maybe<&2, String>) -> Bool:
  match xs held:
    case Nil{} _:
      True{}
    case x <> Nil{} None{}:
      True{}
    case _ _:
      False{}

def fits_alone(xs: List<&2, String>, e: {fits(xs, None{}) == True{} : Bool}) -> {T.at_most_one(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> Nil{}:
      {==}
    case x <> y <> more:
      e

# The path this entry holds is the one queried.
def fits_here(xs: List<&2, String>, +f: String, +p: String, +q: String, +held: List<&2, T.Fact>, none: {T.stated(held, p) == None{} : Maybe<&2, String>}, pq: {String.eq(p, q) == True{} : Bool}, ih: {fits(xs, Some{f}) == True{} : Bool}) -> {fits(f <> xs, T.stated(held, q)) == True{} : Bool}:
  match xs:
    case Nil{}:
      %S.eq_true(p, q, pq) : {fits([f], T.stated(held, _)) == True{} : Bool}
      %Equal.sym(Maybe<&2, String>, T.stated(held, p), None{}, none) : {fits([f], _) == True{} : Bool}
      {==}
    case x <> Nil{}:
      Empty.absurd({fits(f <> x <> Nil{}, T.stated(held, q)) == True{} : Bool}, S.false_true(ih))
    case x <> y <> more:
      Empty.absurd({fits(f <> x <> y <> more, T.stated(held, q)) == True{} : Bool}, S.false_true(ih))

def fits_step(b: Bool, +f: String, +p: String, +q: String, +held: List<&2, T.Fact>, +rest: T.Tree(), none: {T.stated(held, p) == None{} : Maybe<&2, String>}, eb: {String.eq(p, q) == b : Bool}, ih: {fits(T.at(rest, q), Bool.pick(Maybe<&2, String>, b, Some{f}, T.stated(held, q))) == True{} : Bool}) -> {fits(Rev.keep(b, f, T.at(rest, q)), T.stated(held, q)) == True{} : Bool}:
  match b:
    case True{}:
      fits_here(T.at(rest, q), f, p, q, held, none, eb, ih)
    case False{}:
      ih

# The step: the entry's path is not held yet, or the check refused.
def fits_taken(o: Maybe<&2, String>, +f: String, +p: String, +q: String, +held: List<&2, T.Fact>, +rest: T.Tree(), eo: {T.stated(held, p) == o : Maybe<&2, String>}, e: {Result.bind(&2, &2, T.Fault, Unit, Unit, T.taken_one(o, f, p), _ => T.path_taken(rest, T.Fact{p, f} <> held)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, ih: {T.path_taken(rest, T.Fact{p, f} <> held) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>} -> {fits(T.at(rest, q), T.stated(T.Fact{p, f} <> held, q)) == True{} : Bool}) -> {fits(Rev.keep(String.eq(p, q), f, T.at(rest, q)), T.stated(held, q)) == True{} : Bool}:
  match o:
    case Some{other}:
      Empty.absurd({fits(Rev.keep(String.eq(p, q), f, T.at(rest, q)), T.stated(held, q)) == True{} : Bool}, fail_done(T.PathTaken{p, f, other}, e))
    case None{}:
      fits_step(String.eq(p, q), f, p, q, held, rest, eo, {==}, ih(e))

def path_fits(es: T.Tree(), +q: String, +held: List<&2, T.Fact>, e: {T.path_taken(es, held) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {fits(T.at(es, q), T.stated(held, q)) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case T.Entry{+f, +p, k, y, g, m} <> +rest:
      fits_taken(T.stated(held, p), f, p, q, held, rest, {==}, e, x => path_fits(rest, q, T.Fact{p, f} <> held, x))

# No link left dangling
# ---------------------

def some_none(e: T.Entry, d: {None{} == Some{e} : Maybe<&2, T.Entry>}) -> Empty:
  %d : {somedisc(_) : Type}
  Unit{}

def bind_first(r: Result<&2, &2, T.Fault, Unit>, +rest: T.Tree(), +t2: T.Tree(), e: {Result.bind(&2, &2, T.Fault, Unit, Unit, r, _ => T.dangling(rest, t2)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {r == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, fail_done(x, e))
    case Done{u}:
      match u:
        case Unit{}:
          {==}

def bind_rest(r: Result<&2, &2, T.Fault, Unit>, +rest: T.Tree(), +t2: T.Tree(), e: {Result.bind(&2, &2, T.Fault, Unit, Unit, r, _ => T.dangling(rest, t2)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling(rest, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match r:
    case Fail{x}:
      Empty.absurd({T.dangling(rest, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, fail_done(x, e))
    case Done{u}:
      e

def ensure_true(b: Bool, x: T.Fault, e: {T.ensure(b, x) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, fail_done(x, e))

# A file held is held after any insert.
def holds_insert.of(b: Bool, +t: T.Tree(), +e: T.Entry, +x: String, eb: {String.eq(T.entry_file(e), x) == b : Bool}, h: {T.holds(t, x) == True{} : Bool}) -> {T.holds(T.insert(t, e), x) == True{} : Bool}:
  match b:
    case True{}:
      %S.eq_true(T.entry_file(e), x, eb) : {T.holds(T.insert(t, e), _) == True{} : Bool}
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.insert(t, e), T.entry_file(e)), Some{e}, lookup_insert(t, e)) : {Maybe.is_some(&2, T.Entry, _) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.insert(t, e), x), T.lookup(t, x), lookup_other(t, e, x, eb)) : {Maybe.is_some(&2, T.Entry, _) == True{} : Bool}
      h

def holds_insert(+t: T.Tree(), +e: T.Entry, +x: String, h: {T.holds(t, x) == True{} : Bool}) -> {T.holds(T.insert(t, e), x) == True{} : Bool}:
  holds_insert.of(String.eq(T.entry_file(e), x), t, e, x, {==}, h)

# One entry's reference, checked against a tree, is checked against the
# tree with anything inserted.
def one_insert(g: Maybe<&2, T.Target>, +f: String, +t: T.Tree(), +e: T.Entry, ok: {T.dangling_one(T.reference(g), f, t) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling_one(T.reference(g), f, T.insert(t, e)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match g:
    case None{}:
      {==}
    case Some{T.Verbatim{s}}:
      {==}
    case Some{T.Reference{+target}}:
      %Equal.sym(Bool, T.holds(T.insert(t, e), target), True{}, holds_insert(t, e, target, ensure_true(T.holds(t, target), T.Dangling{f, target}, ok))) : {T.ensure(_, T.Dangling{f, target}) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
      {==}

# Every entry checked against a tree is checked against the tree with
# anything inserted.
def dangling_insert(es: T.Tree(), +t: T.Tree(), +e: T.Entry, +d: {T.dangling(es, t) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling(es, T.insert(t, e)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match es:
    case Nil{}:
      {==}
    case T.Entry{+f, p, k, y, +g, m} <> +rest:
      %Equal.sym(Result<&2, &2, T.Fault, Unit>, T.dangling_one(T.reference(g), f, T.insert(t, e)), Done{Unit{}}, one_insert(g, f, t, e, bind_first(T.dangling_one(T.reference(g), f, t), rest, t, d))) : {Result.bind(&2, &2, T.Fault, Unit, Unit, _, _ => T.dangling(rest, T.insert(t, e))) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
      dangling_insert(rest, t, e, bind_rest(T.dangling_one(T.reference(g), f, t), rest, t, d))

# An entry whose own reference checks, inserted among entries that check.
def dangling_cons.at(c: Cmp, e: T.Entry, first: T.Entry, +rest: T.Tree(), +t2: T.Tree(), +d: {T.dangling(first <> rest, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, de: {T.dangling_one(T.reference(T.entry_target(e)), T.entry_file(e), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, ih: {T.dangling(rest, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>} -> {T.dangling(T.insert(rest, e), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling(T.insert.at(c, e, first, rest, T.insert(rest, e)), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match c:
    case LT{}:
      match e:
        case T.Entry{+f, p, k, y, +g, m}:
          %Equal.sym(Result<&2, &2, T.Fault, Unit>, T.dangling_one(T.reference(g), f, t2), Done{Unit{}}, de) : {Result.bind(&2, &2, T.Fault, Unit, Unit, _, _ => T.dangling(first <> rest, t2)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
          d
    case EQ{}:
      match e first:
        case T.Entry{+f, p, k, y, +g, m} T.Entry{+f2, p2, k2, y2, +g2, m2}:
          %Equal.sym(Result<&2, &2, T.Fault, Unit>, T.dangling_one(T.reference(g), f, t2), Done{Unit{}}, de) : {Result.bind(&2, &2, T.Fault, Unit, Unit, _, _ => T.dangling(rest, t2)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
          bind_rest(T.dangling_one(T.reference(g2), f2, t2), rest, t2, d)
    case GT{}:
      match first:
        case T.Entry{+f2, p2, k2, y2, +g2, m2}:
          %Equal.sym(Result<&2, &2, T.Fault, Unit>, T.dangling_one(T.reference(g2), f2, t2), Done{Unit{}}, bind_first(T.dangling_one(T.reference(g2), f2, t2), rest, t2, d)) : {Result.bind(&2, &2, T.Fault, Unit, Unit, _, _ => T.dangling(T.insert(rest, e), t2)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
          ih(bind_rest(T.dangling_one(T.reference(g2), f2, t2), rest, t2, d))

def dangling_cons(es: T.Tree(), +e: T.Entry, +t2: T.Tree(), +d: {T.dangling(es, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, +de: {T.dangling_one(T.reference(T.entry_target(e)), T.entry_file(e), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling(T.insert(es, e), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match es:
    case Nil{}:
      match e:
        case T.Entry{+f, p, k, y, +g, m}:
          %Equal.sym(Result<&2, &2, T.Fault, Unit>, T.dangling_one(T.reference(g), f, t2), Done{Unit{}}, de) : {Result.bind(&2, &2, T.Fault, Unit, Unit, _, _ => T.dangling(Nil{}, t2)) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
          {==}
    case +first <> +rest:
      dangling_cons.at(String.order(T.entry_file(e), T.entry_file(first)), e, first, rest, t2, d, de, x => dangling_cons(rest, e, t2, x, de))

# An entry a lookup found was among those checked.
def unwrap(m: Maybe<&2, T.Entry>) -> T.Entry:
  match m:
    case None{}:
      T.Entry{"", "", T.Lines{}, None{}, None{}, T.Plain{}}
    case Some{e}:
      e

def lookup_ok.of(b: Bool, +f: String, p: String, k: T.FileKind, y: Maybe<&2, String>, +g: Maybe<&2, T.Target>, m: T.Mode, +rest: T.Tree(), +t2: T.Tree(), +x: String, +e0: T.Entry, l: {Bool.pick(Maybe<&2, T.Entry>, b, Some{T.Entry{f, p, k, y, g, m}}, T.lookup(rest, x)) == Some{e0} : Maybe<&2, T.Entry>}, +d: {T.dangling(T.Entry{f, p, k, y, g, m} <> rest, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, ih: {T.lookup(rest, x) == Some{e0} : Maybe<&2, T.Entry>} -> {T.dangling(rest, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>} -> {T.dangling_one(T.reference(T.entry_target(e0)), T.entry_file(e0), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling_one(T.reference(T.entry_target(e0)), T.entry_file(e0), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match b:
    case True{}:
      %Equal.cong(Maybe<&2, T.Entry>, T.Entry, m => unwrap(m), Some{T.Entry{f, p, k, y, g, m}}, Some{e0}, l) : {T.dangling_one(T.reference(T.entry_target(_)), T.entry_file(_), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
      bind_first(T.dangling_one(T.reference(g), f, t2), rest, t2, d)
    case False{}:
      ih(l, bind_rest(T.dangling_one(T.reference(g), f, t2), rest, t2, d))

def lookup_ok(t: T.Tree(), +t2: T.Tree(), +x: String, +e0: T.Entry, l: {T.lookup(t, x) == Some{e0} : Maybe<&2, T.Entry>}, +d: {T.dangling(t, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling_one(T.reference(T.entry_target(e0)), T.entry_file(e0), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match t:
    case Nil{}:
      Empty.absurd({T.dangling_one(T.reference(T.entry_target(e0)), T.entry_file(e0), t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, some_none(e0, l))
    case T.Entry{+f, p, k, y, +g, m} <> +rest:
      lookup_ok.of(String.eq(f, x), f, p, k, y, g, m, rest, t2, x, e0, l, d, l2 => d2 => lookup_ok(rest, t2, x, e0, l2, d2))

# A payload restated leaves every reference checked: the entry it
# rewrites keeps its target, and the tree it lands in holds every file
# the old one held.
def payloads_whole(k: T.FileKind, +f: String, +p0: String, +y0: Maybe<&2, String>, +g: Maybe<&2, T.Target>, +m: T.Mode, +file: String, +y: String, +added: List<&2, String>, +t: T.Tree(), +t2: T.Tree(), +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == Some{T.Entry{f, p0, k, y0, g, m}} : Maybe<&2, T.Entry>}, pe: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.payload_kind(k, T.Entry{f, p0, k, y0, g, m}, file, y, t), t3 => T.payloads(rest, added, t3)) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, +d: {T.dangling(t, t) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, ih: @t3: T.Tree() -> {T.payloads(rest, added, t3) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.dangling(t3, t3) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>} -> {T.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match k:
    case T.Whole{}:
      ih(T.insert(t, T.Entry{f, p0, T.Whole{}, Some{y}, g, m}), pe, dangling_cons(t, T.Entry{f, p0, T.Whole{}, Some{y}, g, m}, T.insert(t, T.Entry{f, p0, T.Whole{}, Some{y}, g, m}), dangling_insert(t, t, T.Entry{f, p0, T.Whole{}, Some{y}, g, m}, d), one_insert(g, f, t, T.Entry{f, p0, T.Whole{}, Some{y}, g, m}, lookup_ok(t, t, file, T.Entry{f, p0, T.Whole{}, y0, g, m}, efound, d))))
    case T.Lines{}:
      Empty.absurd({T.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, fail_tree(T.WrongKind{"bytes", file, T.Lines{}}, t2, pe))
    case T.Link{}:
      Empty.absurd({T.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, fail_tree(T.WrongKind{"bytes", file, T.Link{}}, t2, pe))

def payloads_step(fresh: Bool, found: Maybe<&2, T.Entry>, +file: String, +y: String, +added: List<&2, String>, +t: T.Tree(), +t2: T.Tree(), +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == found : Maybe<&2, T.Entry>}, pe: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.payload_one(fresh, found, file, y, t), t3 => T.payloads(rest, added, t3)) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, +d: {T.dangling(t, t) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, ih: @t3: T.Tree() -> {T.payloads(rest, added, t3) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.dangling(t3, t3) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>} -> {T.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match fresh found:
    case True{} _:
      ih(t, pe, d)
    case False{} None{}:
      Empty.absurd({T.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, fail_tree(T.Unknown{"bytes", file}, t2, pe))
    case False{} Some{T.Entry{+f, +p0, k, +y0, +g, +m}}:
      payloads_whole(k, f, p0, y0, g, m, file, y, added, t, t2, rest, efound, pe, d, ih)

def payloads_keep(bs: List<&2, T.Fact>, +added: List<&2, String>, +t: T.Tree(), +t2: T.Tree(), pe: {T.payloads(bs, added, t) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, +d: {T.dangling(t, t) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {T.dangling(t2, t2) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match bs:
    case Nil{}:
      %Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r => got(r), Done{t}, Done{t2}, pe) : {T.dangling(_, _) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
      d
    case T.Fact{+file, y} <> +rest:
      payloads_step(Rev.member(added, file), T.lookup(t, file), file, y, added, t, t2, rest, {==}, pe, d, t3 => p3 => d3 => payloads_keep(rest, added, t3, t2, p3, d3))

# What a revision leaves
# ----------------------

# Well-formed: no reference dangles and no path is held twice. The two
# checks `apply` runs on its result, as one Bool.
def wf(+t: T.Tree()) -> Bool:
  Bool.and(Result.is_done(&2, &2, T.Fault, Unit, T.dangling(t, t)), Result.is_done(&2, &2, T.Fault, Unit, T.path_taken(t, Nil{})))

def is_done_unit(r: Result<&2, &2, T.Fault, Unit>, e: {Result.is_done(&2, &2, T.Fault, Unit, r) == True{} : Bool}) -> {r == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, S.false_true(e))
    case Done{u}:
      match u:
        case Unit{}:
          {==}

def and_left(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, S.false_true(e))

def and_right(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, S.false_true(e))

def wf_dangling(+t: T.Tree(), e: {wf(t) == True{} : Bool}) -> {T.dangling(t, t) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  is_done_unit(T.dangling(t, t), and_left(Result.is_done(&2, &2, T.Fault, Unit, T.dangling(t, t)), Result.is_done(&2, &2, T.Fault, Unit, T.path_taken(t, Nil{})), e))

def wf_paths(+t: T.Tree(), e: {wf(t) == True{} : Bool}) -> {T.path_taken(t, Nil{}) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  is_done_unit(T.path_taken(t, Nil{}), and_right(Result.is_done(&2, &2, T.Fault, Unit, T.dangling(t, t)), Result.is_done(&2, &2, T.Fault, Unit, T.path_taken(t, Nil{})), e))

def wf_of(+t: T.Tree(), d: {T.dangling(t, t) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, p: {T.path_taken(t, Nil{}) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}) -> {wf(t) == True{} : Bool}:
  %Equal.sym(Result<&2, &2, T.Fault, Unit>, T.dangling(t, t), Done{Unit{}}, d) : {Bool.and(Result.is_done(&2, &2, T.Fault, Unit, _), Result.is_done(&2, &2, T.Fault, Unit, T.path_taken(t, Nil{}))) == True{} : Bool}
  %Equal.sym(Result<&2, &2, T.Fault, Unit>, T.path_taken(t, Nil{}), Done{Unit{}}, p) : {Bool.and(True{}, Result.is_done(&2, &2, T.Fault, Unit, _)) == True{} : Bool}
  {==}

# The stages of `apply`, opened from the last back to the first.
def taken_inv(r: Result<&2, &2, T.Fault, Unit>, +t6: T.Tree(), +t2: T.Tree(), e: {T.apply.taken(r, t6) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {t6 == t2 : T.Tree()}:
  match r:
    case Fail{x}:
      Empty.absurd({t6 == t2 : T.Tree()}, fail_tree(x, t2, e))
    case Done{u}:
      Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r2 => got(r2), Done{t6}, Done{t2}, e)

def taken_ok(r: Result<&2, &2, T.Fault, Unit>, +t6: T.Tree(), +t2: T.Tree(), e: {T.apply.taken(r, t6) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {r == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, fail_tree(x, t2, e))
    case Done{u}:
      match u:
        case Unit{}:
          {==}

def payloads_inv(r: Result<&2, &2, T.Fault, T.Tree()>, +t2: T.Tree(), e: {T.apply.payloads(r) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {r == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}:
  match r:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, fail_tree(x, t2, e))
    case Done{+t6}:
      Equal.cong(T.Tree(), Result<&2, &2, T.Fault, T.Tree()>, t => Done{t}, t6, t2, taken_inv(T.path_taken(t6, Nil{}), t6, t2, e))

def payloads_paths(r: Result<&2, &2, T.Fault, T.Tree()>, +t2: T.Tree(), +e: {T.apply.payloads(r) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {T.path_taken(t2, Nil{}) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match r:
    case Fail{x}:
      Empty.absurd({T.path_taken(t2, Nil{}) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, fail_tree(x, t2, e))
    case Done{+t6}:
      %taken_inv(T.path_taken(t6, Nil{}), t6, t2, e) : {T.path_taken(_, Nil{}) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}
      taken_ok(T.path_taken(t6, Nil{}), t6, t2, e)

def edits_inv(r: Result<&2, &2, T.Fault, Unit>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t5: T.Tree(), +t2: T.Tree(), e: {T.apply.edits(r, fs, added, t5) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {T.payloads(T.facts_of(fs, "bytes"), added, t5) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}:
  match r:
    case Fail{x}:
      Empty.absurd({T.payloads(T.facts_of(fs, "bytes"), added, t5) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, fail_tree(x, t2, e))
    case Done{u}:
      payloads_inv(T.payloads(T.facts_of(fs, "bytes"), added, t5), t2, e)

def edits_paths(r: Result<&2, &2, T.Fault, Unit>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t5: T.Tree(), +t2: T.Tree(), e: {T.apply.edits(r, fs, added, t5) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {T.path_taken(t2, Nil{}) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}:
  match r:
    case Fail{x}:
      Empty.absurd({T.path_taken(t2, Nil{}) == Done{Unit{}} : Result<&2, &2, T.Fault, Unit>}, fail_tree(x, t2, e))
    case Done{u}:
      payloads_paths(T.payloads(T.facts_of(fs, "bytes"), added, t5), t2, e)

def dangling_wf(r: Result<&2, &2, T.Fault, Unit>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t5: T.Tree(), +t2: T.Tree(), er: {T.dangling(t5, t5) == r : Result<&2, &2, T.Fault, Unit>}, +e: {T.apply.dangling(r, fs, added, t5) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {wf(t2) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({wf(t2) == True{} : Bool}, fail_tree(x, t2, e))
    case Done{u}:
      match u:
        case Unit{}:
          wf_of(t2, payloads_keep(T.facts_of(fs, "bytes"), added, t5, t2, edits_inv(T.edits(T.fact_files(T.facts_of(fs, "edit")), t5), fs, added, t5, t2, e), er), edits_paths(T.edits(T.fact_files(T.facts_of(fs, "edit")), t5), fs, added, t5, t2, e))

def drops_wf(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t2: T.Tree(), +e: {T.apply.drops(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {wf(t2) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({wf(t2) == True{} : Bool}, fail_tree(x, t2, e))
    case Done{+t5}:
      dangling_wf(T.dangling(t5, t5), fs, added, t5, t2, {==}, e)

def links_wf(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t2: T.Tree(), +e: {T.apply.links(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {wf(t2) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({wf(t2) == True{} : Bool}, fail_tree(x, t2, e))
    case Done{t4}:
      drops_wf(T.drops(T.fact_files(T.facts_of(fs, "drop")), t4), fs, added, t2, e)

def modes_wf(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t2: T.Tree(), +e: {T.apply.modes(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {wf(t2) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({wf(t2) == True{} : Bool}, fail_tree(x, t2, e))
    case Done{t3}:
      links_wf(T.links(T.facts_of(fs, "link"), added, t3), fs, added, t2, e)

def moves_wf(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t2: T.Tree(), +e: {T.apply.moves(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {wf(t2) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({wf(t2) == True{} : Bool}, fail_tree(x, t2, e))
    case Done{t3}:
      modes_wf(T.modes(T.facts_of(fs, "mode"), added, t3), fs, added, t2, e)

def adds_wf(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t2: T.Tree(), +e: {T.apply.adds(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {wf(t2) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({wf(t2) == True{} : Bool}, fail_tree(x, t2, e))
    case Done{t1}:
      moves_wf(T.moves(T.facts_of(fs, "move"), t1), fs, added, t2, e)

# The file set a revision leaves is well-formed, whatever it was given.
def apply_wf(+t: T.Tree(), r: Rev.Rev, +t2: T.Tree(), +e: {T.apply(t, r) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}) -> {wf(t2) == True{} : Bool}:
  match r:
    case Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, +fs, message}:
      adds_wf(T.adds(T.facts_of(fs, "add"), T.facts_of(fs, "bytes"), T.facts_of(fs, "link"), T.facts_of(fs, "mode"), t), fs, T.fact_files(T.facts_of(fs, "add")), t2, e)

# One line of history, from nothing.
def replay_step(a: Result<&2, &2, T.Fault, T.Tree()>, +t0: T.Tree(), r: Rev.Rev, +rest: List<&2, Rev.Rev>, +t: T.Tree(), ea: {T.apply(t0, r) == a : Result<&2, &2, T.Fault, T.Tree()>}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), a, t2 => T.replay.go(rest, t2)) == Done{t} : Result<&2, &2, T.Fault, T.Tree()>}, ih: @t2: T.Tree() -> {T.replay.go(rest, t2) == Done{t} : Result<&2, &2, T.Fault, T.Tree()>} -> {wf(t2) == True{} : Bool} -> {wf(t) == True{} : Bool}) -> {wf(t) == True{} : Bool}:
  match a:
    case Fail{x}:
      Empty.absurd({wf(t) == True{} : Bool}, fail_tree(x, t, e))
    case Done{+t2}:
      ih(t2, e, apply_wf(t0, r, t2, ea))

def replay_wf.go(rs: List<&2, Rev.Rev>, +t0: T.Tree(), +t: T.Tree(), e: {T.replay.go(rs, t0) == Done{t} : Result<&2, &2, T.Fault, T.Tree()>}, w: {wf(t0) == True{} : Bool}) -> {wf(t) == True{} : Bool}:
  match rs:
    case Nil{}:
      %Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r => got(r), Done{t0}, Done{t}, e) : {wf(_) == True{} : Bool}
      w
    case +r <> +rest:
      replay_step(T.apply(t0, r), t0, r, rest, t, {==}, e, t2 => e2 => w2 => replay_wf.go(rest, t2, t, e2, w2))

def replay_wf(+rs: List<&2, Rev.Rev>, +t: T.Tree(), e: {T.replay(rs) == Done{t} : Result<&2, &2, T.Fault, T.Tree()>}) -> {wf(t) == True{} : Bool}:
  replay_wf.go(rs, T.empty(), t, e, {==})

# A move a drop follows
# ---------------------

# Restating an entry and then removing its file is removing its file.
def remove_insert.at(c: Cmp, e: T.Entry, first: T.Entry, +rest: T.Tree(), ec: {String.order(T.entry_file(e), T.entry_file(first)) == c : Cmp}, ih: {T.remove(T.insert(rest, e), T.entry_file(e)) == T.remove(rest, T.entry_file(e)) : T.Tree()}) -> {T.remove(T.insert.at(c, e, first, rest, T.insert(rest, e)), T.entry_file(e)) == T.remove(first <> rest, T.entry_file(e)) : T.Tree()}:
  match c:
    case LT{}:
      match e:
        case T.Entry{+f, p, k, y, g, m}:
          %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {T.keep(~T.Entry, Bool.not(_), T.Entry{f, p, k, y, g, m}, T.remove(first <> rest, f)) == T.remove(first <> rest, f) : T.Tree()}
          {==}
    case EQ{}:
      match e first:
        case T.Entry{+f, p, k, y, g, m} T.Entry{+f2, p2, k2, y2, g2, m2}:
          %S.order_eq(f, f2, ec) : {T.keep(~T.Entry, Bool.not(String.eq(f, f)), T.Entry{f, p, k, y, g, m}, T.remove(rest, f)) == T.keep(~T.Entry, Bool.not(String.eq(_, f)), T.Entry{_, p2, k2, y2, g2, m2}, T.remove(rest, f)) : T.Tree()}
          %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {T.keep(~T.Entry, Bool.not(_), T.Entry{f, p, k, y, g, m}, T.remove(rest, f)) == T.keep(~T.Entry, Bool.not(_), T.Entry{f, p2, k2, y2, g2, m2}, T.remove(rest, f)) : T.Tree()}
          {==}
    case GT{}:
      match first:
        case T.Entry{+f2, p2, k2, y2, g2, m2}:
          %Equal.sym(T.Tree(), T.remove(T.insert(rest, e), T.entry_file(e)), T.remove(rest, T.entry_file(e)), ih) : {T.keep(~T.Entry, Bool.not(String.eq(f2, T.entry_file(e))), T.Entry{f2, p2, k2, y2, g2, m2}, _) == T.keep(~T.Entry, Bool.not(String.eq(f2, T.entry_file(e))), T.Entry{f2, p2, k2, y2, g2, m2}, T.remove(rest, T.entry_file(e))) : T.Tree()}
          {==}

def remove_insert(t: T.Tree(), +e: T.Entry) -> {T.remove(T.insert(t, e), T.entry_file(e)) == T.remove(t, T.entry_file(e)) : T.Tree()}:
  match t:
    case Nil{}:
      match e:
        case T.Entry{+f, p, k, y, g, m}:
          %Equal.sym(Bool, String.eq(f, f), True{}, S.eq_refl(f)) : {T.keep(~T.Entry, Bool.not(_), T.Entry{f, p, k, y, g, m}, Nil{}) == Nil{} : T.Tree()}
          {==}
    case +first <> +rest:
      remove_insert.at(String.order(T.entry_file(e), T.entry_file(first)), e, first, rest, {==}, remove_insert(rest, e))

# The kind is fixed at the add
# ---------------------------

def kind_eq_refl(k: T.FileKind) -> {T.kind_eq(k, k) == True{} : Bool}:
  match k:
    case T.Lines{}:
      {==}
    case T.Whole{}:
      {==}
    case T.Link{}:
      {==}

# An entry found under a file is that file's.
def lookup_file.of(b: Bool, +f: String, p: String, k: T.FileKind, y: Maybe<&2, String>, g: Maybe<&2, T.Target>, m: T.Mode, +rest: T.Tree(), +file: String, +e0: T.Entry, eb: {String.eq(f, file) == b : Bool}, l: {Bool.pick(Maybe<&2, T.Entry>, b, Some{T.Entry{f, p, k, y, g, m}}, T.lookup(rest, file)) == Some{e0} : Maybe<&2, T.Entry>}, ih: {T.lookup(rest, file) == Some{e0} : Maybe<&2, T.Entry>} -> {T.entry_file(e0) == file : String}) -> {T.entry_file(e0) == file : String}:
  match b:
    case True{}:
      %Equal.cong(Maybe<&2, T.Entry>, T.Entry, m2 => unwrap(m2), Some{T.Entry{f, p, k, y, g, m}}, Some{e0}, l) : {T.entry_file(_) == file : String}
      S.eq_true(f, file, eb)
    case False{}:
      ih(l)

def lookup_file(t: T.Tree(), +file: String, +e0: T.Entry, l: {T.lookup(t, file) == Some{e0} : Maybe<&2, T.Entry>}) -> {T.entry_file(e0) == file : String}:
  match t:
    case Nil{}:
      Empty.absurd({T.entry_file(e0) == file : String}, some_none(e0, l))
    case T.Entry{+f, p, k, y, g, m} <> +rest:
      lookup_file.of(String.eq(f, file), f, p, k, y, g, m, rest, file, e0, {==}, l, l2 => lookup_file(rest, file, e0, l2))

# Restating an entry the tree holds, kind unchanged, changes no kind.
def kind_insert.of(b: Bool, +t: T.Tree(), +f: String, p: String, +k: T.FileKind, y: Maybe<&2, String>, g: Maybe<&2, T.Target>, m: T.Mode, p2: String, y2: Maybe<&2, String>, g2: Maybe<&2, T.Target>, m2: T.Mode, +file: String, +x: String, eb: {String.eq(f, x) == b : Bool}, +efound: {T.lookup(t, file) == Some{T.Entry{f, p, k, y, g, m}} : Maybe<&2, T.Entry>}) -> {T.kind(T.insert(t, T.Entry{f, p2, k, y2, g2, m2}), x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match b:
    case True{}:
      %S.eq_true(f, x, eb) : {T.kind(T.insert(t, T.Entry{f, p2, k, y2, g2, m2}), _) == T.kind(t, _) : Maybe<&2, T.FileKind>}
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.insert(t, T.Entry{f, p2, k, y2, g2, m2}), f), Some{T.Entry{f, p2, k, y2, g2, m2}}, lookup_insert(t, T.Entry{f, p2, k, y2, g2, m2})) : {Maybe.map(&2, T.Entry, T.FileKind, e => T.entry_kind(e), _) == T.kind(t, f) : Maybe<&2, T.FileKind>}
      %Equal.sym(String, f, file, lookup_file(t, file, T.Entry{f, p, k, y, g, m}, efound)) : {Some{k} == T.kind(t, _) : Maybe<&2, T.FileKind>}
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(t, file), Some{T.Entry{f, p, k, y, g, m}}, efound) : {Some{k} == Maybe.map(&2, T.Entry, T.FileKind, e => T.entry_kind(e), _) : Maybe<&2, T.FileKind>}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.insert(t, T.Entry{f, p2, k, y2, g2, m2}), x), T.lookup(t, x), lookup_other(t, T.Entry{f, p2, k, y2, g2, m2}, x, eb)) : {Maybe.map(&2, T.Entry, T.FileKind, e => T.entry_kind(e), _) == T.kind(t, x) : Maybe<&2, T.FileKind>}
      {==}

def kind_insert(+t: T.Tree(), +f: String, p: String, +k: T.FileKind, y: Maybe<&2, String>, g: Maybe<&2, T.Target>, m: T.Mode, p2: String, y2: Maybe<&2, String>, g2: Maybe<&2, T.Target>, m2: T.Mode, +file: String, +x: String, efound: {T.lookup(t, file) == Some{T.Entry{f, p, k, y, g, m}} : Maybe<&2, T.Entry>}) -> {T.kind(T.insert(t, T.Entry{f, p2, k, y2, g2, m2}), x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  kind_insert.of(String.eq(f, x), t, f, p, k, y, g, m, p2, y2, g2, m2, file, x, {==}, efound)

# Removing a file leaves it unfound, and every other file as it was.
def remove_same.of(b: Bool, +f: String, p: String, k: T.FileKind, y: Maybe<&2, String>, g: Maybe<&2, T.Target>, m: T.Mode, +rest: T.Tree(), +file: String, eb: {String.eq(f, file) == b : Bool}, ih: {T.lookup(T.remove(rest, file), file) == None{} : Maybe<&2, T.Entry>}) -> {T.lookup(T.keep(~T.Entry, Bool.not(b), T.Entry{f, p, k, y, g, m}, T.remove(rest, file)), file) == None{} : Maybe<&2, T.Entry>}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, String.eq(f, file), False{}, eb) : {Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p, k, y, g, m}}, T.lookup(T.remove(rest, file), file)) == None{} : Maybe<&2, T.Entry>}
      ih

def remove_same(t: T.Tree(), +file: String) -> {T.lookup(T.remove(t, file), file) == None{} : Maybe<&2, T.Entry>}:
  match t:
    case Nil{}:
      {==}
    case T.Entry{+f, p, k, y, g, m} <> +rest:
      remove_same.of(String.eq(f, file), f, p, k, y, g, m, rest, file, {==}, remove_same(rest, file))

def remove_other.of(b: Bool, +f: String, p: String, k: T.FileKind, y: Maybe<&2, String>, g: Maybe<&2, T.Target>, m: T.Mode, +rest: T.Tree(), +file: String, +x: String, eb: {String.eq(f, file) == b : Bool}, ne: {String.eq(file, x) == False{} : Bool}, ih: {T.lookup(T.remove(rest, file), x) == T.lookup(rest, x) : Maybe<&2, T.Entry>}) -> {T.lookup(T.keep(~T.Entry, Bool.not(b), T.Entry{f, p, k, y, g, m}, T.remove(rest, file)), x) == T.lookup(T.Entry{f, p, k, y, g, m} <> rest, x) : Maybe<&2, T.Entry>}:
  match b:
    case True{}:
      %Equal.sym(String, f, file, S.eq_true(f, file, eb)) : {T.lookup(T.remove(rest, file), x) == Bool.pick(Maybe<&2, T.Entry>, String.eq(_, x), Some{T.Entry{f, p, k, y, g, m}}, T.lookup(rest, x)) : Maybe<&2, T.Entry>}
      %Equal.sym(Bool, String.eq(file, x), False{}, ne) : {T.lookup(T.remove(rest, file), x) == Bool.pick(Maybe<&2, T.Entry>, _, Some{T.Entry{f, p, k, y, g, m}}, T.lookup(rest, x)) : Maybe<&2, T.Entry>}
      ih
    case False{}:
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.remove(rest, file), x), T.lookup(rest, x), ih) : {Bool.pick(Maybe<&2, T.Entry>, String.eq(f, x), Some{T.Entry{f, p, k, y, g, m}}, _) == Bool.pick(Maybe<&2, T.Entry>, String.eq(f, x), Some{T.Entry{f, p, k, y, g, m}}, T.lookup(rest, x)) : Maybe<&2, T.Entry>}
      {==}

def remove_other(t: T.Tree(), +file: String, +x: String, +ne: {String.eq(file, x) == False{} : Bool}) -> {T.lookup(T.remove(t, file), x) == T.lookup(t, x) : Maybe<&2, T.Entry>}:
  match t:
    case Nil{}:
      {==}
    case T.Entry{+f, p, k, y, g, m} <> +rest:
      remove_other.of(String.eq(f, file), f, p, k, y, g, m, rest, file, x, {==}, ne, remove_other(rest, file, x, ne))

def kind_remove.of(b: Bool, +t: T.Tree(), +file: String, +x: String, +k: T.FileKind, eb: {String.eq(file, x) == b : Bool}, h: {T.kind_kept(k, T.kind(t, x)) == True{} : Bool}) -> {T.kind_kept(k, T.kind(T.remove(t, file), x)) == True{} : Bool}:
  match b:
    case True{}:
      %S.eq_true(file, x, eb) : {T.kind_kept(k, T.kind(T.remove(t, file), _)) == True{} : Bool}
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.remove(t, file), file), None{}, remove_same(t, file)) : {T.kind_kept(k, Maybe.map(&2, T.Entry, T.FileKind, e => T.entry_kind(e), _)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.remove(t, file), x), T.lookup(t, x), remove_other(t, file, x, eb)) : {T.kind_kept(k, Maybe.map(&2, T.Entry, T.FileKind, e => T.entry_kind(e), _)) == True{} : Bool}
      h

def kind_remove(+t: T.Tree(), +file: String, +x: String, +k: T.FileKind, h: {T.kind_kept(k, T.kind(t, x)) == True{} : Bool}) -> {T.kind_kept(k, T.kind(T.remove(t, file), x)) == True{} : Bool}:
  kind_remove.of(String.eq(file, x), t, file, x, k, {==}, h)

def kinddisc(m: Maybe<&2, T.FileKind>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{k}:
      Empty

def kind_none(k: T.FileKind, d: {None{} == Some{k} : Maybe<&2, T.FileKind>}) -> Empty:
  %d : {kinddisc(_) : Type}
  Unit{}

def kind_add.held(l: Maybe<&2, T.Entry>, k: T.FileKind, v: {Maybe.is_some(&2, T.Entry, l) == False{} : Bool}, h: {Maybe.map(&2, T.Entry, T.FileKind, e => T.entry_kind(e), l) == Some{k} : Maybe<&2, T.FileKind>}) -> Empty:
  match l:
    case None{}:
      kind_none(k, h)
    case Some{e0}:
      S.true_false(v)

def kind_add.fresh(+t: T.Tree(), +e: T.Entry, +x: String, eq: {T.entry_file(e) == x : String}, fresh: {T.holds(t, T.entry_file(e)) == False{} : Bool}) -> {Maybe.is_some(&2, T.Entry, T.lookup(t, x)) == False{} : Bool}:
  %eq : {Maybe.is_some(&2, T.Entry, T.lookup(t, _)) == False{} : Bool}
  fresh

# A file added is a file the tree did not hold, so the others keep theirs.
def kind_add.of(b: Bool, +t: T.Tree(), +e: T.Entry, +x: String, +k: T.FileKind, eb: {String.eq(T.entry_file(e), x) == b : Bool}, fresh: {T.holds(t, T.entry_file(e)) == False{} : Bool}, h: {T.kind(t, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind(T.insert(t, e), x) == Some{k} : Maybe<&2, T.FileKind>}:
  match b:
    case True{}:
      Empty.absurd({T.kind(T.insert(t, e), x) == Some{k} : Maybe<&2, T.FileKind>}, kind_add.held(T.lookup(t, x), k, kind_add.fresh(t, e, x, S.eq_true(T.entry_file(e), x, eb), fresh), h))
    case False{}:
      %Equal.sym(Maybe<&2, T.Entry>, T.lookup(T.insert(t, e), x), T.lookup(t, x), lookup_other(t, e, x, eb)) : {Maybe.map(&2, T.Entry, T.FileKind, e2 => T.entry_kind(e2), _) == Some{k} : Maybe<&2, T.FileKind>}
      h

def kind_add(+t: T.Tree(), +e: T.Entry, +x: String, +k: T.FileKind, fresh: {T.holds(t, T.entry_file(e)) == False{} : Bool}, h: {T.kind(t, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind(T.insert(t, e), x) == Some{k} : Maybe<&2, T.FileKind>}:
  kind_add.of(String.eq(T.entry_file(e), x), t, e, x, k, {==}, fresh, h)

# The loops, one key at a time.
def adds_step(hb: Bool, +file: String, +p: String, +bytes: List<&2, T.Fact>, +links: List<&2, T.Fact>, +ms: List<&2, T.Fact>, +t: T.Tree(), +t1: T.Tree(), +x: String, +k: T.FileKind, +rest: List<&2, T.Fact>, ehb: {T.holds(t, file) == hb : Bool}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.add_one(hb, file, p, Maybe.map(&2, String, T.Target, s => T.target_of(s), T.stated(links, file)), T.stated(bytes, file), T.mode_stated(T.stated(ms, file)), t), t2 => T.adds(rest, bytes, links, ms, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind(t, x) == Some{k} : Maybe<&2, T.FileKind>}, ih: @t2: T.Tree() -> {T.adds(rest, bytes, links, ms, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind(t2, x) == Some{k} : Maybe<&2, T.FileKind>} -> {T.kind(t1, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == Some{k} : Maybe<&2, T.FileKind>}:
  match hb:
    case True{}:
      Empty.absurd({T.kind(t1, x) == Some{k} : Maybe<&2, T.FileKind>}, fail_tree(T.AddedTwice{file}, t1, e))
    case False{}:
      ih(T.insert(t, T.Entry{file, p, T.kind_of(Maybe.map(&2, String, T.Target, s => T.target_of(s), T.stated(links, file)), T.stated(bytes, file)), T.stated(bytes, file), Maybe.map(&2, String, T.Target, s => T.target_of(s), T.stated(links, file)), T.mode_stated(T.stated(ms, file))}), e, kind_add(t, T.Entry{file, p, T.kind_of(Maybe.map(&2, String, T.Target, s => T.target_of(s), T.stated(links, file)), T.stated(bytes, file)), T.stated(bytes, file), Maybe.map(&2, String, T.Target, s => T.target_of(s), T.stated(links, file)), T.mode_stated(T.stated(ms, file))}, x, k, ehb, h))

def adds_kinds(as: List<&2, T.Fact>, +bytes: List<&2, T.Fact>, +links: List<&2, T.Fact>, +ms: List<&2, T.Fact>, +t: T.Tree(), +t1: T.Tree(), +x: String, +k: T.FileKind, e: {T.adds(as, bytes, links, ms, t) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind(t, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == Some{k} : Maybe<&2, T.FileKind>}:
  match as:
    case Nil{}:
      %Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r => got(r), Done{t}, Done{t1}, e) : {T.kind(_, x) == Some{k} : Maybe<&2, T.FileKind>}
      h
    case T.Fact{+file, +p} <> +rest:
      adds_step(T.holds(t, file), file, p, bytes, links, ms, t, t1, x, k, rest, {==}, e, h, t2 => e2 => h2 => adds_kinds(rest, bytes, links, ms, t2, t1, x, k, e2, h2))

def moves_step(found: Maybe<&2, T.Entry>, +file: String, +p: String, +t: T.Tree(), +t1: T.Tree(), +x: String, +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == found : Maybe<&2, T.Entry>}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.move_one(found, file, p, t), t2 => T.moves(rest, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, ih: @t2: T.Tree() -> {T.moves(rest, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind(t1, x) == T.kind(t2, x) : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match found:
    case None{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.Unknown{"move", file}, t1, e))
    case Some{T.Entry{+f, +p0, +k0, +y, +g, +m}}:
      Equal.trans(Maybe<&2, T.FileKind>, T.kind(t1, x), T.kind(T.insert(t, T.Entry{f, p, k0, y, g, m}), x), T.kind(t, x), ih(T.insert(t, T.Entry{f, p, k0, y, g, m}), e), kind_insert(t, f, p0, k0, y, g, m, p, y, g, m, file, x, efound))

def moves_kinds(mvs: List<&2, T.Fact>, +t: T.Tree(), +t1: T.Tree(), +x: String, e: {T.moves(mvs, t) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match mvs:
    case Nil{}:
      %Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r => got(r), Done{t}, Done{t1}, e) : {T.kind(_, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}
      {==}
    case T.Fact{+file, +p} <> +rest:
      moves_step(T.lookup(t, file), file, p, t, t1, x, rest, {==}, e, t2 => e2 => moves_kinds(rest, t2, t1, x, e2))

def modes_kind(k0: T.FileKind, +f: String, +p0: String, +y: Maybe<&2, String>, +g: Maybe<&2, T.Target>, +m0: T.Mode, +file: String, +m: String, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == Some{T.Entry{f, p0, k0, y, g, m0}} : Maybe<&2, T.Entry>}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.mode_kind(k0, T.Entry{f, p0, k0, y, g, m0}, file, m, t), t2 => T.modes(rest, added, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, ih: @t2: T.Tree() -> {T.modes(rest, added, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind(t1, x) == T.kind(t2, x) : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match k0:
    case T.Link{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.WrongKind{"mode", file, T.Link{}}, t1, e))
    case T.Lines{}:
      Equal.trans(Maybe<&2, T.FileKind>, T.kind(t1, x), T.kind(T.insert(t, T.Entry{f, p0, T.Lines{}, y, g, T.mode_of(m)}), x), T.kind(t, x), ih(T.insert(t, T.Entry{f, p0, T.Lines{}, y, g, T.mode_of(m)}), e), kind_insert(t, f, p0, T.Lines{}, y, g, m0, p0, y, g, T.mode_of(m), file, x, efound))
    case T.Whole{}:
      Equal.trans(Maybe<&2, T.FileKind>, T.kind(t1, x), T.kind(T.insert(t, T.Entry{f, p0, T.Whole{}, y, g, T.mode_of(m)}), x), T.kind(t, x), ih(T.insert(t, T.Entry{f, p0, T.Whole{}, y, g, T.mode_of(m)}), e), kind_insert(t, f, p0, T.Whole{}, y, g, m0, p0, y, g, T.mode_of(m), file, x, efound))

def modes_step(fresh: Bool, found: Maybe<&2, T.Entry>, +file: String, +m: String, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == found : Maybe<&2, T.Entry>}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.mode_one(fresh, found, file, m, t), t2 => T.modes(rest, added, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, ih: @t2: T.Tree() -> {T.modes(rest, added, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind(t1, x) == T.kind(t2, x) : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match fresh found:
    case True{} _:
      ih(t, e)
    case False{} None{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.Unknown{"mode", file}, t1, e))
    case False{} Some{T.Entry{+f, +p0, k0, +y, +g, +m0}}:
      modes_kind(k0, f, p0, y, g, m0, file, m, added, t, t1, x, rest, efound, e, ih)

def modes_kinds(ms: List<&2, T.Fact>, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, e: {T.modes(ms, added, t) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match ms:
    case Nil{}:
      %Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r => got(r), Done{t}, Done{t1}, e) : {T.kind(_, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}
      {==}
    case T.Fact{+file, +m} <> +rest:
      modes_step(Rev.member(added, file), T.lookup(t, file), file, m, added, t, t1, x, rest, {==}, e, t2 => e2 => modes_kinds(rest, added, t2, t1, x, e2))

def links_kind(k0: T.FileKind, +f: String, +p0: String, +y: Maybe<&2, String>, +g: Maybe<&2, T.Target>, +m0: T.Mode, +file: String, +g2: String, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == Some{T.Entry{f, p0, k0, y, g, m0}} : Maybe<&2, T.Entry>}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.link_kind(k0, T.Entry{f, p0, k0, y, g, m0}, file, g2, t), t2 => T.links(rest, added, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, ih: @t2: T.Tree() -> {T.links(rest, added, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind(t1, x) == T.kind(t2, x) : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match k0:
    case T.Link{}:
      Equal.trans(Maybe<&2, T.FileKind>, T.kind(t1, x), T.kind(T.insert(t, T.Entry{f, p0, T.Link{}, y, Some{T.target_of(g2)}, m0}), x), T.kind(t, x), ih(T.insert(t, T.Entry{f, p0, T.Link{}, y, Some{T.target_of(g2)}, m0}), e), kind_insert(t, f, p0, T.Link{}, y, g, m0, p0, y, Some{T.target_of(g2)}, m0, file, x, efound))
    case T.Lines{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.WrongKind{"link", file, T.Lines{}}, t1, e))
    case T.Whole{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.WrongKind{"link", file, T.Whole{}}, t1, e))

def links_step(fresh: Bool, found: Maybe<&2, T.Entry>, +file: String, +g2: String, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == found : Maybe<&2, T.Entry>}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.link_one(fresh, found, file, g2, t), t2 => T.links(rest, added, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, ih: @t2: T.Tree() -> {T.links(rest, added, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind(t1, x) == T.kind(t2, x) : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match fresh found:
    case True{} _:
      ih(t, e)
    case False{} None{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.Unknown{"link", file}, t1, e))
    case False{} Some{T.Entry{+f, +p0, k0, +y, +g, +m0}}:
      links_kind(k0, f, p0, y, g, m0, file, g2, added, t, t1, x, rest, efound, e, ih)

def links_kinds(ls: List<&2, T.Fact>, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, e: {T.links(ls, added, t) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match ls:
    case Nil{}:
      %Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r => got(r), Done{t}, Done{t1}, e) : {T.kind(_, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}
      {==}
    case T.Fact{+file, +g2} <> +rest:
      links_step(Rev.member(added, file), T.lookup(t, file), file, g2, added, t, t1, x, rest, {==}, e, t2 => e2 => links_kinds(rest, added, t2, t1, x, e2))

def payloads_kind(k0: T.FileKind, +f: String, +p0: String, +y0: Maybe<&2, String>, +g: Maybe<&2, T.Target>, +m0: T.Mode, +file: String, +y: String, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == Some{T.Entry{f, p0, k0, y0, g, m0}} : Maybe<&2, T.Entry>}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.payload_kind(k0, T.Entry{f, p0, k0, y0, g, m0}, file, y, t), t2 => T.payloads(rest, added, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, ih: @t2: T.Tree() -> {T.payloads(rest, added, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind(t1, x) == T.kind(t2, x) : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match k0:
    case T.Whole{}:
      Equal.trans(Maybe<&2, T.FileKind>, T.kind(t1, x), T.kind(T.insert(t, T.Entry{f, p0, T.Whole{}, Some{y}, g, m0}), x), T.kind(t, x), ih(T.insert(t, T.Entry{f, p0, T.Whole{}, Some{y}, g, m0}), e), kind_insert(t, f, p0, T.Whole{}, y0, g, m0, p0, Some{y}, g, m0, file, x, efound))
    case T.Lines{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.WrongKind{"bytes", file, T.Lines{}}, t1, e))
    case T.Link{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.WrongKind{"bytes", file, T.Link{}}, t1, e))

def payloads_kstep(fresh: Bool, found: Maybe<&2, T.Entry>, +file: String, +y: String, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, +rest: List<&2, T.Fact>, efound: {T.lookup(t, file) == found : Maybe<&2, T.Entry>}, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.payload_one(fresh, found, file, y, t), t2 => T.payloads(rest, added, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, ih: @t2: T.Tree() -> {T.payloads(rest, added, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind(t1, x) == T.kind(t2, x) : Maybe<&2, T.FileKind>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match fresh found:
    case True{} _:
      ih(t, e)
    case False{} None{}:
      Empty.absurd({T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}, fail_tree(T.Unknown{"bytes", file}, t1, e))
    case False{} Some{T.Entry{+f, +p0, k0, +y0, +g, +m0}}:
      payloads_kind(k0, f, p0, y0, g, m0, file, y, added, t, t1, x, rest, efound, e, ih)

def payloads_kinds(bs: List<&2, T.Fact>, +added: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, e: {T.payloads(bs, added, t) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}) -> {T.kind(t1, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}:
  match bs:
    case Nil{}:
      %Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r => got(r), Done{t}, Done{t1}, e) : {T.kind(_, x) == T.kind(t, x) : Maybe<&2, T.FileKind>}
      {==}
    case T.Fact{+file, +y} <> +rest:
      payloads_kstep(Rev.member(added, file), T.lookup(t, file), file, y, added, t, t1, x, rest, {==}, e, t2 => e2 => payloads_kinds(rest, added, t2, t1, x, e2))

def drops_step(held: Bool, +file: String, +t: T.Tree(), +t1: T.Tree(), +x: String, +k: T.FileKind, +rest: List<&2, String>, e: {Result.bind(&2, &2, T.Fault, T.Tree(), T.Tree(), T.drop_one(held, file, t), t2 => T.drops(rest, t2)) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind_kept(k, T.kind(t, x)) == True{} : Bool}, ih: @t2: T.Tree() -> {T.drops(rest, t2) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>} -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool} -> {T.kind_kept(k, T.kind(t1, x)) == True{} : Bool}) -> {T.kind_kept(k, T.kind(t1, x)) == True{} : Bool}:
  match held:
    case False{}:
      Empty.absurd({T.kind_kept(k, T.kind(t1, x)) == True{} : Bool}, fail_tree(T.Unknown{"drop", file}, t1, e))
    case True{}:
      ih(T.remove(t, file), e, kind_remove(t, file, x, k, h))

def drops_kinds(ds: List<&2, String>, +t: T.Tree(), +t1: T.Tree(), +x: String, +k: T.FileKind, e: {T.drops(ds, t) == Done{t1} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind_kept(k, T.kind(t, x)) == True{} : Bool}) -> {T.kind_kept(k, T.kind(t1, x)) == True{} : Bool}:
  match ds:
    case Nil{}:
      %Equal.cong(Result<&2, &2, T.Fault, T.Tree()>, T.Tree(), r => got(r), Done{t}, Done{t1}, e) : {T.kind_kept(k, T.kind(_, x)) == True{} : Bool}
      h
    case +file <> +rest:
      drops_step(T.holds(t, file), file, t, t1, x, k, rest, e, h, t2 => e2 => h2 => drops_kinds(rest, t2, t1, x, k, e2, h2))

def kept_of(+k: T.FileKind, m: Maybe<&2, T.FileKind>, h: {m == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind_kept(k, m) == True{} : Bool}:
  %Equal.sym(Maybe<&2, T.FileKind>, m, Some{k}, h) : {T.kind_kept(k, _) == True{} : Bool}
  kind_eq_refl(k)

# The stages of `apply`, first to last: a file's kind is the one it had
# through every stage that restates an entry, and the one it had or gone
# once the drops are applied.
def payloads_stage(r: Result<&2, &2, T.Fault, T.Tree()>, +bs: List<&2, T.Fact>, +added: List<&2, String>, +t5: T.Tree(), +t2: T.Tree(), +x: String, +k: T.FileKind, er: {T.payloads(bs, added, t5) == r : Result<&2, &2, T.Fault, T.Tree()>}, +e: {T.apply.payloads(r) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind_kept(k, T.kind(t5, x)) == True{} : Bool}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}, fail_tree(f, t2, e))
    case Done{+t6}:
      %taken_inv(T.path_taken(t6, Nil{}), t6, t2, e) : {T.kind_kept(k, T.kind(_, x)) == True{} : Bool}
      %Equal.sym(Maybe<&2, T.FileKind>, T.kind(t6, x), T.kind(t5, x), payloads_kinds(bs, added, t5, t6, x, er)) : {T.kind_kept(k, _) == True{} : Bool}
      h

def edits_stage(r: Result<&2, &2, T.Fault, Unit>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t5: T.Tree(), +t2: T.Tree(), +x: String, +k: T.FileKind, e: {T.apply.edits(r, fs, added, t5) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind_kept(k, T.kind(t5, x)) == True{} : Bool}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}, fail_tree(f, t2, e))
    case Done{u}:
      payloads_stage(T.payloads(T.facts_of(fs, "bytes"), added, t5), T.facts_of(fs, "bytes"), added, t5, t2, x, k, {==}, e, h)

def dangling_stage(r: Result<&2, &2, T.Fault, Unit>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t5: T.Tree(), +t2: T.Tree(), +x: String, +k: T.FileKind, e: {T.apply.dangling(r, fs, added, t5) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind_kept(k, T.kind(t5, x)) == True{} : Bool}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}, fail_tree(f, t2, e))
    case Done{u}:
      edits_stage(T.edits(T.fact_files(T.facts_of(fs, "edit")), t5), fs, added, t5, t2, x, k, e, h)

def drops_stage(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t4: T.Tree(), +t2: T.Tree(), +x: String, +k: T.FileKind, er: {T.drops(T.fact_files(T.facts_of(fs, "drop")), t4) == r : Result<&2, &2, T.Fault, T.Tree()>}, e: {T.apply.drops(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind(t4, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}, fail_tree(f, t2, e))
    case Done{+t5}:
      dangling_stage(T.dangling(t5, t5), fs, added, t5, t2, x, k, e, drops_kinds(T.fact_files(T.facts_of(fs, "drop")), t4, t5, x, k, er, kept_of(k, T.kind(t4, x), h)))

def links_stage(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t3: T.Tree(), +t2: T.Tree(), +x: String, +k: T.FileKind, er: {T.links(T.facts_of(fs, "link"), added, t3) == r : Result<&2, &2, T.Fault, T.Tree()>}, e: {T.apply.links(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind(t3, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}, fail_tree(f, t2, e))
    case Done{+t4}:
      drops_stage(T.drops(T.fact_files(T.facts_of(fs, "drop")), t4), fs, added, t4, t2, x, k, {==}, e, Equal.trans(Maybe<&2, T.FileKind>, T.kind(t4, x), T.kind(t3, x), Some{k}, links_kinds(T.facts_of(fs, "link"), added, t3, t4, x, er), h))

def modes_stage(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t1: T.Tree(), +t2: T.Tree(), +x: String, +k: T.FileKind, er: {T.modes(T.facts_of(fs, "mode"), added, t1) == r : Result<&2, &2, T.Fault, T.Tree()>}, e: {T.apply.modes(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind(t1, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}, fail_tree(f, t2, e))
    case Done{+t3}:
      links_stage(T.links(T.facts_of(fs, "link"), added, t3), fs, added, t3, t2, x, k, {==}, e, Equal.trans(Maybe<&2, T.FileKind>, T.kind(t3, x), T.kind(t1, x), Some{k}, modes_kinds(T.facts_of(fs, "mode"), added, t1, t3, x, er), h))

def moves_stage(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +added: List<&2, String>, +t1: T.Tree(), +t2: T.Tree(), +x: String, +k: T.FileKind, er: {T.moves(T.facts_of(fs, "move"), t1) == r : Result<&2, &2, T.Fault, T.Tree()>}, e: {T.apply.moves(r, fs, added) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind(t1, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}, fail_tree(f, t2, e))
    case Done{+t3}:
      modes_stage(T.modes(T.facts_of(fs, "mode"), added, t3), fs, added, t3, t2, x, k, {==}, e, Equal.trans(Maybe<&2, T.FileKind>, T.kind(t3, x), T.kind(t1, x), Some{k}, moves_kinds(T.facts_of(fs, "move"), t1, t3, x, er), h))

def adds_stage(r: Result<&2, &2, T.Fault, T.Tree()>, +fs: List<&2, Rev.Header>, +t: T.Tree(), +t2: T.Tree(), +x: String, +k: T.FileKind, er: {T.adds(T.facts_of(fs, "add"), T.facts_of(fs, "bytes"), T.facts_of(fs, "link"), T.facts_of(fs, "mode"), t) == r : Result<&2, &2, T.Fault, T.Tree()>}, e: {T.apply.adds(r, fs, T.fact_files(T.facts_of(fs, "add"))) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind(t, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Fail{f}:
      Empty.absurd({T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}, fail_tree(f, t2, e))
    case Done{+t1}:
      moves_stage(T.moves(T.facts_of(fs, "move"), t1), fs, T.fact_files(T.facts_of(fs, "add")), t1, t2, x, k, {==}, e, adds_kinds(T.facts_of(fs, "add"), T.facts_of(fs, "bytes"), T.facts_of(fs, "link"), T.facts_of(fs, "mode"), t, t1, x, k, er, h))

# A file's kind is the one it was added with, at every revision it
# survives.
def apply_kinds(+t: T.Tree(), r: Rev.Rev, +t2: T.Tree(), +x: String, +k: T.FileKind, e: {T.apply(t, r) == Done{t2} : Result<&2, &2, T.Fault, T.Tree()>}, h: {T.kind(t, x) == Some{k} : Maybe<&2, T.FileKind>}) -> {T.kind_kept(k, T.kind(t2, x)) == True{} : Bool}:
  match r:
    case Rev.Rev{change, parents, supersedes, author, when, revised_by, revised, +fs, message}:
      adds_stage(T.adds(T.facts_of(fs, "add"), T.facts_of(fs, "bytes"), T.facts_of(fs, "link"), T.facts_of(fs, "mode"), t), fs, t, t2, x, k, {==}, e, h)

def main() -> IO(Unit):
  IO.print("ok")
