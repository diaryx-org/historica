// The C side of `Store.tidy`. The adapter is `store_locate.c`'s; the
// compiler splices both into one program, so the declaration is enough.
#include <stdint.h>

typedef int32_t (*HistCall)(const char* in, size_t in_len, char** out, size_t* out_len);
static Term hist_run(Env e, Term arg, IoWork* w, HistCall call);

extern int32_t hist_store_tidy(const char* query, size_t query_len, char** out, size_t* out_len);

Term store_tidy_run(Env e, Term* f, IoWork* w) {
  return hist_run(e, f[0], w, hist_store_tidy);
}

static void __attribute__((constructor)) store_tidy_use(void) {
  io_eff(CID_STORE_TIDY, store_tidy_run, 0);
}
