# Refusals are justified: a replay `Block.replay_ops` refuses has a cause
# `Block.cause` names, and one with no cause replays to the positional
# result. Each cause is read off the parent and the operations alone.
import Base
import ./ops.bend as Ops
import ./text.bend as T
import ./replay_spec.bend as Spec
import ./cursor_spec.bend as Cursor
import ./semantic_replay.bend as Block
import ./composition_lemmas.bend as Comp
import ./diff_lemmas.bend as Diff

def rdisc(r: Result<&2, &2, String, List<&2, Ops.Item>>) -> Type:
  match r:
    case Fail{msg}:
      Empty
    case Done{xs}:
      Unit

def done_fail(-xs: List<&2, Ops.Item>, -msg: String, e: {Done{xs} == Fail{msg} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> Empty:
  %e : {rdisc(_) : Type}
  Unit{}

# `Ops.apply.checked`, its decisions named.
def checked_is(+r: List<&2, Ops.Item>, stated: Maybe<&2, String>) -> {Ops.apply.checked(stated, r) == Diff.after_checks(r, Ops.terminated_but_last(r), Ops.check_result(stated, r)) : Result<&2, &2, String, List<&2, Ops.Item>>}:
  {==}

# The digest check, its decisions named.
def digest_is(+d: String, +r: List<&2, Ops.Item>, forgot: Bool, same: Bool, ef: {Ops.any_forgotten(r) == forgot : Bool}, es: {T.same(d, Ops.state_digest(r)) == same : Bool}) -> {Ops.check_result(Some{d}, r) == Bool.pick(Result<&2, &2, String, Unit>, Bool.or(forgot, same), Done{Unit{}}, Fail{"the result stated is " ++ d ++ " but the replay produced " ++ Ops.state_digest(r)}) : Result<&2, &2, String, Unit>}:
  match forgot:
    case True{}:
      %Equal.sym(Bool, Ops.any_forgotten(r), True{}, ef) : {Ops.check_result.of(d, _, Ops.state_digest(r)) == Done{Unit{}} : Result<&2, &2, String, Unit>}
      {==}
    case False{}:
      %Equal.sym(Bool, Ops.any_forgotten(r), False{}, ef) : {Ops.check_result.of(d, _, Ops.state_digest(r)) == Bool.pick(Result<&2, &2, String, Unit>, same, Done{Unit{}}, Fail{"the result stated is " ++ d ++ " but the replay produced " ++ Ops.state_digest(r)}) : Result<&2, &2, String, Unit>}
      %Equal.sym(Bool, T.same(d, Ops.state_digest(r)), same, es) : {Bool.pick(Result<&2, &2, String, Unit>, _, Done{Unit{}}, Fail{"the result stated is " ++ d ++ " but the replay produced " ++ Ops.state_digest(r)}) == Bool.pick(Result<&2, &2, String, Unit>, same, Done{Unit{}}, Fail{"the result stated is " ++ d ++ " but the replay produced " ++ Ops.state_digest(r)}) : Result<&2, &2, String, Unit>}
      {==}

def not_or(forgot: Bool, same: Bool) -> {Bool.and(Bool.not(forgot), Bool.not(same)) == Bool.not(Bool.or(forgot, same)) : Bool}:
  match forgot:
    case True{}:
      {==}
    case False{}:
      match same:
        case True{}:
          {==}
        case False{}:
          {==}

# What the digest cause is, its decisions named.
def mismatch_is(+d: String, +r: List<&2, Ops.Item>, forgot: Bool, same: Bool, ef: {Ops.any_forgotten(r) == forgot : Bool}, es: {T.same(d, Ops.state_digest(r)) == same : Bool}) -> {Block.digest_mismatch(Some{d}, r) == Bool.not(Bool.or(forgot, same)) : Bool}:
  %Equal.sym(Bool, Ops.any_forgotten(r), forgot, ef) : {Bool.and(Bool.not(_), Bool.not(T.same(d, Ops.state_digest(r)))) == Bool.not(Bool.or(forgot, same)) : Bool}
  %Equal.sym(Bool, T.same(d, Ops.state_digest(r)), same, es) : {Bool.and(Bool.not(forgot), Bool.not(_)) == Bool.not(Bool.or(forgot, same)) : Bool}
  not_or(forgot, same)

# The last two checks, over the named decisions.
def tail_refused(+r: List<&2, Ops.Item>, tb: Bool, dig: Result<&2, &2, String, Unit>, -msg: String, e: {Diff.after_checks(r, tb, dig) == Fail{msg} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Bool.or(Bool.not(tb), Result.is_fail(&2, &2, String, Unit, dig)) == True{} : Bool}:
  match tb:
    case False{}:
      {==}
    case True{}:
      match dig:
        case Fail{m}:
          {==}
        case Done{u}:
          Empty.absurd({False{} == True{} : Bool}, done_fail(r, msg, e))

def tail_accepted(+r: List<&2, Ops.Item>, tb: Bool, dig: Result<&2, &2, String, Unit>, e: {Bool.or(Bool.not(tb), Result.is_fail(&2, &2, String, Unit, dig)) == False{} : Bool}) -> {Diff.after_checks(r, tb, dig) == Done{r} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match tb:
    case False{}:
      Empty.absurd({Diff.after_checks(r, False{}, dig) == Done{r} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(Equal.sym(Bool, True{}, False{}, e)))
    case True{}:
      match dig:
        case Fail{m}:
          Empty.absurd({Diff.after_checks(r, True{}, Fail{m}) == Done{r} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(Equal.sym(Bool, True{}, False{}, e)))
        case Done{Unit{}}:
          {==}

def fail_of_pick(b: Bool, -m: String) -> {Result.is_fail(&2, &2, String, Unit, Bool.pick(Result<&2, &2, String, Unit>, b, Done{Unit{}}, Fail{m})) == Bool.not(b) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# The digest cause is exactly the digest check failing.
def mismatch_fail(stated: Maybe<&2, String>, +r: List<&2, Ops.Item>) -> {Block.digest_mismatch(stated, r) == Result.is_fail(&2, &2, String, Unit, Ops.check_result(stated, r)) : Bool}:
  match stated:
    case None{}:
      {==}
    case Some{+d}:
      +forgot = Ops.any_forgotten(r)
      +same = T.same(d, Ops.state_digest(r))
      %Equal.sym(Result<&2, &2, String, Unit>, Ops.check_result(Some{d}, r), Bool.pick(Result<&2, &2, String, Unit>, Bool.or(forgot, same), Done{Unit{}}, Fail{"the result stated is " ++ d ++ " but the replay produced " ++ Ops.state_digest(r)}), digest_is(d, r, forgot, same, {==}, {==})) : {Block.digest_mismatch(Some{d}, r) == Result.is_fail(&2, &2, String, Unit, _) : Bool}
      %Equal.sym(Bool, Result.is_fail(&2, &2, String, Unit, Bool.pick(Result<&2, &2, String, Unit>, Bool.or(forgot, same), Done{Unit{}}, Fail{"the result stated is " ++ d ++ " but the replay produced " ++ Ops.state_digest(r)})), Bool.not(Bool.or(forgot, same)), fail_of_pick(Bool.or(forgot, same), "the result stated is " ++ d ++ " but the replay produced " ++ Ops.state_digest(r))) : {Block.digest_mismatch(Some{d}, r) == _ : Bool}
      mismatch_is(d, r, forgot, same, {==}, {==})

def or_cast(-a: Bool, -b: Bool, -a2: Bool, -b2: Bool, ea: {a == a2 : Bool}, eb: {b == b2 : Bool}, e: {Bool.or(a, b) == False{} : Bool}) -> {Bool.or(a2, b2) == False{} : Bool}:
  %ea : {Bool.or(_, b2) == False{} : Bool}
  %eb : {Bool.or(a, _) == False{} : Bool}
  e

# A refusal past the range and cursor checks has the newline or digest cause.
def refused.tail(+r: List<&2, Ops.Item>, +stated: Maybe<&2, String>, -msg: String, e: {Diff.after_checks(r, Ops.terminated_but_last(r), Ops.check_result(stated, r)) == Fail{msg} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Bool.or(Bool.not(Ops.terminated_but_last(r)), Block.digest_mismatch(stated, r)) == True{} : Bool}:
  %Equal.sym(Bool, Block.digest_mismatch(stated, r), Result.is_fail(&2, &2, String, Unit, Ops.check_result(stated, r)), mismatch_fail(stated, r)) : {Bool.or(Bool.not(Ops.terminated_but_last(r)), _) == True{} : Bool}
  tail_refused(r, Ops.terminated_but_last(r), Ops.check_result(stated, r), msg, e)

def accepted.tail(+r: List<&2, Ops.Item>, +stated: Maybe<&2, String>, e: {Bool.or(Bool.not(Ops.terminated_but_last(r)), Block.digest_mismatch(stated, r)) == False{} : Bool}) -> {Diff.after_checks(r, Ops.terminated_but_last(r), Ops.check_result(stated, r)) == Done{r} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  tail_accepted(r, Ops.terminated_but_last(r), Ops.check_result(stated, r), or_cast(Bool.not(Ops.terminated_but_last(r)), Block.digest_mismatch(stated, r), Bool.not(Ops.terminated_but_last(r)), Result.is_fail(&2, &2, String, Unit, Ops.check_result(stated, r)), {==}, mismatch_fail(stated, r), e))

# Every refusal of the checked, combined replay has a cause.
def refused.of(in_range: Bool, error: Maybe<&2, String>, +r: List<&2, Ops.Item>, +stated: Maybe<&2, String>, -msg: String, e: {Cursor.checked(in_range, stated, Cursor.combine(error, Nil{}, Done{r})) == Fail{msg} : Result<&2, &2, String, List<&2, Ops.Item>>}) -> {Block.cause.of(in_range, error, r, stated) == True{} : Bool}:
  match in_range:
    case False{}:
      {==}
    case True{}:
      match error:
        case Some{x}:
          {==}
        case None{}:
          refused.tail(r, stated, msg, e)

# And a replay with no cause is the positional result.
def accepted.of(in_range: Bool, error: Maybe<&2, String>, +r: List<&2, Ops.Item>, +stated: Maybe<&2, String>, e: {Block.cause.of(in_range, error, r, stated) == False{} : Bool}) -> {Cursor.checked(in_range, stated, Cursor.combine(error, Nil{}, Done{r})) == Done{r} : Result<&2, &2, String, List<&2, Ops.Item>>}:
  match in_range:
    case False{}:
      Empty.absurd({Cursor.checked(False{}, stated, Cursor.combine(error, Nil{}, Done{r})) == Done{r} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(Equal.sym(Bool, True{}, False{}, e)))
    case True{}:
      match error:
        case Some{x}:
          Empty.absurd({Cursor.checked(True{}, stated, Cursor.combine(Some{x}, Nil{}, Done{r})) == Done{r} : Result<&2, &2, String, List<&2, Ops.Item>>}, Comp.false_true(Equal.sym(Bool, True{}, False{}, e)))
        case None{}:
          accepted.tail(r, stated, e)

def main() -> Unit:
  Unit{}
