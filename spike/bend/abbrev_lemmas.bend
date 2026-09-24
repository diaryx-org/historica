# An abbreviated digest names one revision. `log`, `names` and every message
# that names a revision spell its digest as long as it must be to be unique
# among the store's, and at least eight characters. The abbreviation is a
# prefix of the digest, and no other digest of the same length starts with
# it — however the store's digests share their prefixes.
import Base
import ./commands.bend as Main
import ./revision.bend as Rev
import ./string_lemmas.bend as S
import ./graph_lemmas.bend as GL
import ./bookmark_lemmas.bend as BmL
import ./linear_lemmas.bend as Lin
import ./composition_lemmas.bend as Comp

# Characters and numbers
# ----------------------

def char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{U32{w}}:
      (%Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, S.word_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
        {==})

def ne_sym.at(+x: Char, +y: Char, b: Bool, eb: {Char.is_eq(y, x) == b : Bool}, e: {Char.is_eq(x, y) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, S.true_false(Equal.trans(Bool, True{}, Char.is_eq(x, x), False{}, Equal.sym(Bool, Char.is_eq(x, x), True{}, char_refl(x)),
        (%BmL.chr_eq(y, x, eb) : {Char.is_eq(x, _) == False{} : Bool}
          e))))

def ne_sym(+x: Char, +y: Char, e: {Char.is_eq(x, y) == False{} : Bool}) -> {Char.is_eq(y, x) == False{} : Bool}:
  ne_sym.at(x, y, Char.is_eq(y, x), {==}, e)

def ndisc(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def zero_succ(-n: Nat, e: {0n == 1n+n : Nat}) -> Empty:
  %e : {ndisc(_) : Type}
  Unit{}

def succ_zero(-n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  zero_succ(n, Equal.sym(Nat, 1n+n, 0n, e))

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => pred(n), 1n+a, 1n+b, e)

def ge_le(a: Nat, b: Nat, e: {Nat.is_ge(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, S.false_true(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ge_le(p, q, e)

def lt_succ_of_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, S.false_true(e))
    case 1n+p 1n+q:
      lt_succ_of_le(p, q, e)

# Strings
# -------

def take_prefix(s: String, n: Nat) -> {String.starts_with(s, String.take(s, n)) == True{} : Bool}:
  match s n:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{+h, +t} 1n+p:
      (%Equal.sym(Bool, Char.is_eq(h, h), True{}, char_refl(h)) : {String.starts_with.if(t, String.take(t, p), _) == True{} : Bool}
        take_prefix(t, p))

def pfx_cons(+x: Char, +at: String, +y: Char, +bt: String, b1: Bool, +e1: {Char.is_eq(x, y) == b1 : Bool}, k: Nat, lt: {Nat.is_lt(Bool.pick(Nat, b1, 1n+Main.shared(at, bt), 0n), k) == True{} : Bool}, +len: {String.length(at) == String.length(bt) : Nat}, ne: {SCon{x, at} == SCon{y, bt} : String} -> Empty, ih: @k2: Nat -> {Nat.is_lt(Main.shared(at, bt), k2) == True{} : Bool} -> {String.length(at) == String.length(bt) : Nat} -> ({at == bt : String} -> Empty) -> {String.starts_with(bt, String.take(at, k2)) == False{} : Bool}) -> {String.starts_with(SCon{y, bt}, String.take(SCon{x, at}, k)) == False{} : Bool}:
  match b1:
    case False{}:
      match k:
        case 0n:
          Empty.absurd({String.starts_with(SCon{y, bt}, SNil{}) == False{} : Bool}, S.false_true(lt))
        case 1n+k2:
          (%Equal.sym(Bool, Char.is_eq(y, x), False{}, ne_sym(x, y, e1)) : {String.starts_with.if(bt, String.take(at, k2), _) == False{} : Bool}
            {==})
    case True{}:
      match k:
        case 0n:
          Empty.absurd({String.starts_with(SCon{y, bt}, SNil{}) == False{} : Bool}, S.false_true(lt))
        case 1n+k2:
          (%Equal.sym(Char, x, y, BmL.chr_eq(x, y, e1)) : {String.starts_with.if(bt, String.take(at, k2), Char.is_eq(y, _)) == False{} : Bool}
            (%Equal.sym(Bool, Char.is_eq(y, y), True{}, char_refl(y)) : {String.starts_with.if(bt, String.take(at, k2), _) == False{} : Bool}
              ih(k2, lt, len, h => ne(Equal.trans(String, SCon{x, at}, SCon{y, at}, SCon{y, bt}, Equal.cong(Char, String, c => SCon{c, at}, x, y, BmL.chr_eq(x, y, e1)), Equal.cong(String, String, s => SCon{y, s}, at, bt, h))))))

# Two different strings of one length part within `shared` of each other:
# a prefix of one longer than that is no prefix of the other.
def pfx(a: String, b: String, k: Nat, lt: {Nat.is_lt(Main.shared(a, b), k) == True{} : Bool}, len: {String.length(a) == String.length(b) : Nat}, ne: {a == b : String} -> Empty) -> {String.starts_with(b, String.take(a, k)) == False{} : Bool}:
  match a b:
    case SNil{} SNil{}:
      Empty.absurd({String.starts_with(SNil{}, String.take(SNil{}, k)) == False{} : Bool}, ne({==}))
    case SNil{} SCon{y, bt}:
      Empty.absurd({String.starts_with(SCon{y, bt}, String.take(SNil{}, k)) == False{} : Bool}, zero_succ(String.length(bt), len))
    case SCon{x, at} SNil{}:
      Empty.absurd({String.starts_with(SNil{}, String.take(SCon{x, at}, k)) == False{} : Bool}, succ_zero(String.length(at), len))
    case SCon{+x, +at} SCon{+y, +bt}:
      pfx_cons(x, at, y, bt, Char.is_eq(x, y), {==}, k, lt, succ_inj(String.length(at), String.length(bt), len), ne,
        k2 => lt2 => len2 => ne2 => pfx(at, bt, k2, lt2, len2, ne2))

# The abbreviation
# ----------------

def ls_head(+y: String, +rest: List<&2, String>, +id: String, +o: String, +h: {y == o : String}, +ne: {String.eq(o, id) == False{} : Bool}) -> {Nat.is_le(Main.shared(id, o), Main.longest_shared(id, y <> rest)) == True{} : Bool}:
  (%h : {Nat.is_le(Main.shared(id, _), Nat.max(Bool.pick(Nat, String.eq(y, id), 0n, Main.shared(id, y)), Main.longest_shared(id, rest))) == True{} : Bool}
    (%Equal.sym(Bool, String.eq(y, id), False{}, (%Equal.sym(String, y, o, h) : {String.eq(_, id) == False{} : Bool}
      ne)) : {Nat.is_le(Main.shared(id, y), Nat.max(Bool.pick(Nat, _, 0n, Main.shared(id, y)), Main.longest_shared(id, rest))) == True{} : Bool}
      ge_le(Nat.max(Main.shared(id, y), Main.longest_shared(id, rest)), Main.shared(id, y), Nat.max_ge_l(Main.shared(id, y), Main.longest_shared(id, rest)))))

# Every other digest among these shares no more with this one than the
# longest share.
def ls_ge(among: List<&2, String>, +id: String, +o: String, m: {Rev.member(among, o) == True{} : Bool}, +ne: {String.eq(o, id) == False{} : Bool}) -> {Nat.is_le(Main.shared(id, o), Main.longest_shared(id, among)) == True{} : Bool}:
  match among:
    case Nil{}:
      Empty.absurd({Nat.is_le(Main.shared(id, o), 0n) == True{} : Bool}, S.false_true(m))
    case +y <> +rest:
      GL.member_cons({Nat.is_le(Main.shared(id, o), Main.longest_shared(id, y <> rest)) == True{} : Bool}, y, rest, o, m,
        h => ls_head(y, rest, id, o, h, ne),
        t => Lin.le_trans(Main.shared(id, o), Main.longest_shared(id, rest), Main.longest_shared(id, y <> rest), ls_ge(rest, id, o, t, ne),
          ge_le(Main.longest_shared(id, y <> rest), Main.longest_shared(id, rest), Nat.max_ge_r(Bool.pick(Nat, String.eq(y, id), 0n, Main.shared(id, y)), Main.longest_shared(id, rest)))))

# No other digest of its length starts with the abbreviation.
def unique(+id: String, +among: List<&2, String>, +o: String, m: {Rev.member(among, o) == True{} : Bool}, +ne: {String.eq(o, id) == False{} : Bool}, len: {String.length(o) == String.length(id) : Nat}) -> {String.starts_with(o, Main.abbreviate(id, among)) == False{} : Bool}:
  pfx(id, o, Nat.max(8n, 1n+Main.longest_shared(id, among)),
    Lin.lt_le_trans(Main.shared(id, o), 1n+Main.longest_shared(id, among), Nat.max(8n, 1n+Main.longest_shared(id, among)),
      lt_succ_of_le(Main.shared(id, o), Main.longest_shared(id, among), ls_ge(among, id, o, m, ne)),
      ge_le(Nat.max(8n, 1n+Main.longest_shared(id, among)), 1n+Main.longest_shared(id, among), Nat.max_ge_r(8n, 1n+Main.longest_shared(id, among)))),
    Equal.sym(Nat, String.length(o), String.length(id), len),
    h => S.false_true(Equal.trans(Bool, False{}, String.eq(o, id), True{}, Equal.sym(Bool, String.eq(o, id), False{}, ne),
      (%Equal.sym(String, id, o, h) : {String.eq(o, _) == True{} : Bool}
        S.eq_refl(o)))))

# The abbreviation is a prefix of the digest.
def prefix_ok(+id: String, +among: List<&2, String>) -> {String.starts_with(id, Main.abbreviate(id, among)) == True{} : Bool}:
  take_prefix(id, Nat.max(8n, 1n+Main.longest_shared(id, among)))
