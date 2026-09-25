# A store's header opens whatever its note says, once a blank line sets the
# note apart from the format line — decision 0069's promise, which is what
# lets `init` write a note there, and a person write another.
import Base
import ./store.bend as Store

def noted(+note: String) -> {Store.header.r("historica\n\n" ++ note) == Done{Unit{}} : Result<&2, &2, String, Unit>}:
  {==}
