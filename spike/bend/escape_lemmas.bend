# `fetch` asks for a manifest's path by its bytes, as the Rust tool spells
# them: every byte that is not unreserved written `%` and two uppercase hex
# digits, and `/` kept, since it is the one character of a path that is
# structure rather than content. What it asks for decodes, as a URL's path
# is decoded, back to exactly those bytes, whatever they are, and holds no
# character a URL's path may not hold as it is. Each byte is one of 256,
# and the checker is shown every one of them.
import Base
import ./text.bend as T
import ./fetch.bend as Fetch
import ./string_lemmas.bend as S
import ./anchor_lemmas.bend as AL
import ./composition_lemmas.bend as Comp

# What the laws say
# -----------------

def cons.m(+b: U32, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match rest:
    case None{}:
      None{}
    case Some{r}:
      Some{b <> r}

# A hex digit's value, spelled as RFC 3986 asks a producer to spell an
# escape: `0`-`9` and `A`-`F`.
def hexval(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)), Some{U32.sub(x, 48)},
      Bool.pick(Maybe<&2, U32>, Bool.and(U32.is_ge(x, 65), U32.is_le(x, 70)), Some{U32.sub(x, 55)}, None{}))

def byte.m(hi: Maybe<&2, U32>, lo: Maybe<&2, U32>, rest: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match hi lo:
    case Some{h} Some{l}:
      cons.m(U32.add(U32.mul(h, 16), l), rest)
    case _ _:
      None{}

# Where a decoder is in a URL's path: between escapes, just past a `%`, or
# past an escape's first hex digit.
type Esc is Data:
  Esc.Plain{}
  Esc.Pct{}
  Esc.Half{hi: Maybe<&2, U32>}

def unesc(s: String, st: Esc) -> Maybe<&2, List<&2, U32>>:
  match s:
    case SNil{}:
      match st:
        case Esc.Plain{}:
          Some{Nil{}}
        case Esc.Pct{}:
          None{}
        case Esc.Half{h}:
          None{}
    case SCon{+c, +t}:
      match st:
        case Esc.Plain{}:
          Bool.pick(Maybe<&2, List<&2, U32>>, Char.is_eq(c, '%'), unesc(t, Esc.Pct{}), cons.m(Char.to_u32(c), unesc(t, Esc.Plain{})))
        case Esc.Pct{}:
          unesc(t, Esc.Half{hexval(c)})
        case Esc.Half{h}:
          byte.m(h, hexval(c), unesc(t, Esc.Plain{}))

# A URL's path decoded to its bytes, as RFC 3986 has it: `%` and two hex
# digits the byte they spell, any other character its own code, and
# nothing where an escape is cut short or is not two uppercase hex digits.
def unescaped(s: String) -> Maybe<&2, List<&2, U32>>:
  unesc(s, Esc.Plain{})

# The characters a URL's path may hold as they are: RFC 3986's unreserved
# ones, `/`, and the `%` that opens an escape.
def url_char(+c: Char) -> Bool:
  List.contains(~Char, ~(a => b => Char.is_eq(a, b)), String.to_list("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~/%"), c)

# A byte
# ------

# The low eight bits of a word compared with nothing are never less.
def nlt.fin(c: Cmp, x: Bool, ec: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_lt(Word.cmp.fin(x, False{}, c)) == False{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_lt(Word.cmp.fin(x, False{}, LT{})) == False{} : Bool}, S.true_false(ec))
    case EQ{}:
      match x:
        case True{}:
          {==}
        case False{}:
          {==}
    case GT{}:
      {==}

def nlt(+n: Nat, a: Word(n)) -> {Cmp.is_lt(Word.cmp(n, a, Word.zero(n))) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{x, +t}:
          nlt.fin(Word.cmp(p, t, Word.zero(p)), x, nlt(p, t))

def dec.leaf(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, -rest: String) -> {unescaped(Fetch.escaped.byte(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) ++ rest) == cons.m(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, unescaped(rest)) : Maybe<&2, List<&2, U32>>}:
  match b0:
    case False{}:
      match b1:
        case False{}:
          match b2:
            case False{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
            case True{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
        case True{}:
          match b2:
            case False{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
            case True{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
    case True{}:
      match b1:
        case False{}:
          match b2:
            case False{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
            case True{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
        case True{}:
          match b2:
            case False{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
            case True{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}
                            case True{}:
                              match b7:
                                case False{}:
                                  {==}
                                case True{}:
                                  {==}

def url.leaf(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, -rest: String, hr: {T.all_chars(~(c => url_char(c)), rest) == True{} : Bool}) -> {T.all_chars(~(c => url_char(c)), Fetch.escaped.byte(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) ++ rest) == True{} : Bool}:
  match b0:
    case False{}:
      match b1:
        case False{}:
          match b2:
            case False{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
            case True{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
        case True{}:
          match b2:
            case False{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
            case True{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
    case True{}:
      match b1:
        case False{}:
          match b2:
            case False{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
            case True{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
        case True{}:
          match b2:
            case False{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
            case True{}:
              match b3:
                case False{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                case True{}:
                  match b4:
                    case False{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                    case True{}:
                      match b5:
                        case False{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                        case True{}:
                          match b6:
                            case False{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr
                            case True{}:
                              match b7:
                                case False{}:
                                  hr
                                case True{}:
                                  hr

def cmp_lt(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def is_lt_true(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, S.false_true(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, S.false_true(e))

# Where a word's low bits compared with nothing leave it less, what its
# high bits compared to was less.
def fin_lt(c: Cmp, b: Bool, e: {Cmp.is_lt(Word.cmp.fin(b, False{}, c)) == True{} : Bool}) -> {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match b:
        case True{}:
          Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, S.false_true(e))
        case False{}:
          Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, S.false_true(e))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, S.false_true(e))

def hi_zero.at(c: Cmp, h0: Bool, +ht: Word(23n), ec: {Word.cmp(23n, ht, Word.zero(23n)) == c : Cmp}, e: {Word.cmp.fin(h0, True{}, c) == LT{} : Cmp}) -> {WCon{h0, ht} == Word.zero(24n) : Word(24n)}:
  match c:
    case LT{}:
      Empty.absurd({WCon{h0, ht} == Word.zero(24n) : Word(24n)}, S.false_true(Equal.trans(Bool, False{}, Cmp.is_lt(Word.cmp(23n, ht, Word.zero(23n))), True{}, Equal.sym(Bool, Cmp.is_lt(Word.cmp(23n, ht, Word.zero(23n))), False{}, nlt(23n, ht)), Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), Word.cmp(23n, ht, Word.zero(23n)), LT{}, ec))))
    case EQ{}:
      match h0:
        case False{}:
          Equal.cong(Word(23n), Word(24n), x => WCon{False{}, x}, ht, Word.zero(23n), S.word_eq(23n, ht, Word.zero(23n), ec))
        case True{}:
          Empty.absurd({WCon{True{}, ht} == Word.zero(24n) : Word(24n)}, S.false_true(Equal.cong(Cmp, Bool, x => cmp_lt(x), EQ{}, LT{}, e)))
    case GT{}:
      Empty.absurd({WCon{h0, ht} == Word.zero(24n) : Word(24n)}, S.false_true(Equal.cong(Cmp, Bool, x => cmp_lt(x), GT{}, LT{}, e)))

# A word less than 256 holds nothing above its low eight bits.
def hi_zero(hw: Word(24n), e: {Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)}) == LT{} : Cmp}) -> {hw == Word.zero(24n) : Word(24n)}:
  match hw:
    case WCon{h0, +ht}:
      hi_zero.at(Word.cmp(23n, ht, Word.zero(23n)), h0, ht, {==}, e)

def high_zero(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +hw: Word(24n), h: {U32.is_lt(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, hw}}}}}}}}}, 256) == True{} : Bool}) -> {hw == Word.zero(24n) : Word(24n)}:
  hi_zero(hw, is_lt_true(Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)}), fin_lt(Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)}), b7, fin_lt(Word.cmp.fin(b7, False{}, Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)})), b6, fin_lt(Word.cmp.fin(b6, False{}, Word.cmp.fin(b7, False{}, Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)}))), b5, fin_lt(Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, False{}, Word.cmp.fin(b7, False{}, Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)})))), b4, fin_lt(Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, False{}, Word.cmp.fin(b7, False{}, Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)}))))), b3, fin_lt(Word.cmp.fin(b3, False{}, Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, False{}, Word.cmp.fin(b7, False{}, Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)})))))), b2, fin_lt(Word.cmp.fin(b2, False{}, Word.cmp.fin(b3, False{}, Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, False{}, Word.cmp.fin(b7, False{}, Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)}))))))), b1, fin_lt(Word.cmp.fin(b1, False{}, Word.cmp.fin(b2, False{}, Word.cmp.fin(b3, False{}, Word.cmp.fin(b4, False{}, Word.cmp.fin(b5, False{}, Word.cmp.fin(b6, False{}, Word.cmp.fin(b7, False{}, Word.cmp(24n, hw, WCon{True{}, Word.zero(23n)})))))))), b0, h))))))))))

def dec.byte(b: U32, -rest: String, h: {U32.is_lt(b, 256) == True{} : Bool}) -> {unescaped(Fetch.escaped.byte(b) ++ rest) == cons.m(b, unescaped(rest)) : Maybe<&2, List<&2, U32>>}:
  match b:
    case U32{w}:
      match w:
        case WCon{+b0, t0}:
          match t0:
            case WCon{+b1, t1}:
              match t1:
                case WCon{+b2, t2}:
                  match t2:
                    case WCon{+b3, t3}:
                      match t3:
                        case WCon{+b4, t4}:
                          match t4:
                            case WCon{+b5, t5}:
                              match t5:
                                case WCon{+b6, t6}:
                                  match t6:
                                    case WCon{+b7, +hw}:
                                      %Equal.sym(Word(24n), hw, Word.zero(24n), high_zero(b0, b1, b2, b3, b4, b5, b6, b7, hw, h)) : {unescaped(Fetch.escaped.byte(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}}) ++ rest) == cons.m(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}}, unescaped(rest)) : Maybe<&2, List<&2, U32>>}
                                      dec.leaf(b0, b1, b2, b3, b4, b5, b6, b7, rest)

def url.byte(b: U32, -rest: String, hr: {T.all_chars(~(c => url_char(c)), rest) == True{} : Bool}, h: {U32.is_lt(b, 256) == True{} : Bool}) -> {T.all_chars(~(c => url_char(c)), Fetch.escaped.byte(b) ++ rest) == True{} : Bool}:
  match b:
    case U32{w}:
      match w:
        case WCon{+b0, t0}:
          match t0:
            case WCon{+b1, t1}:
              match t1:
                case WCon{+b2, t2}:
                  match t2:
                    case WCon{+b3, t3}:
                      match t3:
                        case WCon{+b4, t4}:
                          match t4:
                            case WCon{+b5, t5}:
                              match t5:
                                case WCon{+b6, t6}:
                                  match t6:
                                    case WCon{+b7, +hw}:
                                      %Equal.sym(Word(24n), hw, Word.zero(24n), high_zero(b0, b1, b2, b3, b4, b5, b6, b7, hw, h)) : {T.all_chars(~(c => url_char(c)), Fetch.escaped.byte(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}}) ++ rest) == True{} : Bool}
                                      url.leaf(b0, b1, b2, b3, b4, b5, b6, b7, rest, hr)

# The bytes
# ---------

# Every list of bytes escaped decodes back to itself.
def dec_bytes(bs: List<&2, U32>, +h: {List.all(~&2, ~U32, ~(b => U32.is_lt(b, 256)), bs) == True{} : Bool}) -> {unescaped(Fetch.escaped.bytes(bs)) == Some{bs} : Maybe<&2, List<&2, U32>>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      Equal.trans(Maybe<&2, List<&2, U32>>, unescaped(Fetch.escaped.byte(b) ++ Fetch.escaped.bytes(rest)), cons.m(b, unescaped(Fetch.escaped.bytes(rest))), Some{b <> rest},
        dec.byte(b, Fetch.escaped.bytes(rest), Comp.and_left(U32.is_lt(b, 256), List.all(~&2, ~U32, ~(b => U32.is_lt(b, 256)), rest), h)),
        Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, m => cons.m(b, m), unescaped(Fetch.escaped.bytes(rest)), Some{rest}, dec_bytes(rest, Comp.and_right(U32.is_lt(b, 256), List.all(~&2, ~U32, ~(b => U32.is_lt(b, 256)), rest), h))))

# And holds nothing but characters a URL's path may hold.
def url_bytes(bs: List<&2, U32>, +h: {List.all(~&2, ~U32, ~(b => U32.is_lt(b, 256)), bs) == True{} : Bool}) -> {T.all_chars(~(c => url_char(c)), Fetch.escaped.bytes(bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      url.byte(b, Fetch.escaped.bytes(rest), url_bytes(rest, Comp.and_right(U32.is_lt(b, 256), List.all(~&2, ~U32, ~(b => U32.is_lt(b, 256)), rest), h)), Comp.and_left(U32.is_lt(b, 256), List.all(~&2, ~U32, ~(b => U32.is_lt(b, 256)), rest), h))

# The characters RFC 3986 leaves unreserved, and `/`: each is asked for as
# itself.
def kept() -> String:
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~/"

def kept_as_itself() -> {List.all(~&2, ~Char, ~(c => String.eq(Fetch.escaped.byte(Char.to_u32(c)), SCon{c, SNil{}})), String.to_list(kept())) == True{} : Bool}:
  {==}
