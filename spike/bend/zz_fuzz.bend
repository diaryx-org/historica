import Base
import ./text.bend as T
import ./naming.bend as N

def frags() -> List<&2, String>:
  ["", " ", ".", "..", "a", "b c", "Fix: x?", "\t", String.from_list([Chr{160}]), "/", "x.", " .y", "a\\nb", "\r", ". . .", "*", String.from_list([Chr{8232}, Chr{65}]), "one two three four five six seven eight nine ten eleven twelve", "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnop", String.from_list([Chr{7}]), "  x  ", "x .", "héllo wörld"]

def prefixed(+x: String, ys: List<&2, String>) -> List<&2, String>:
  match ys:
    case Nil{}:
      Nil{}
    case y <> rest:
      (x ++ y) <> prefixed(x, rest)

def pairs(xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +x <> rest:
      List.append(&2, String, prefixed(x, ys), pairs(rest, ys))

def check(+when: String, +m: String, +change: String, +id: String) -> List<&2, String>:
  +ok1 = N.in_month(String.take(when, 7n), N.stem(when, m, change, id, Nil{}))
  +ok2 = N.in_month(String.take(when, 7n), N.stem(when, m, change, id, [N.Named{when, m, change}]))
  +ok3 = N.in_month(String.take(when, 7n), N.stem(when, m, change, id, [N.Named{when, m, "zzzzzzzzzz"}]))
  +ok4 = Nat.is_le(String.length(N.summary(m, change)), 60n)
  +ok5 = N.trimmed(N.summary(m, change))
  Bool.pick(List<&2, String>, Bool.and(Bool.and(Bool.and(ok1, ok2), Bool.and(ok3, ok4)), ok5), Nil{}, ["FAIL [" ++ m ++ "] -> [" ++ N.stem(when, m, change, id, [N.Named{when, m, change}]) ++ "] " ++ Bool.show(ok1) ++ Bool.show(ok2) ++ Bool.show(ok3) ++ Bool.show(ok4) ++ Bool.show(ok5)])

def checks(ms: List<&2, String>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> rest:
      List.append(&2, String, check("2025-08-19T00:47:11-06:00", m, "qpvuntsmwlrkzxonmvtplsyq", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"), checks(rest))

def main() -> IO(Unit):
  +ms = pairs(pairs(frags(), frags()), frags())
  do IO<Unit>:
    IO.print("cases " ++ Nat.show(List.length(&2, String, ms)))
    IO.print(String.join(checks(ms), "\n"))
    IO.print("done")
