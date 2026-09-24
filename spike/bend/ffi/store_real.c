// The C side of `Store.real`. The adapter is `store_locate.c`'s; the
// compiler splices both into one program, so the declaration is enough.
#include <stdint.h>

typedef int32_t (*HistCall)(const char* in, size_t in_len, char** out, size_t* out_len);
static Term hist_run(Env e, Term arg, IoWork* w, HistCall call);

extern int32_t hist_path_real(const char* query, size_t query_len, char** out, size_t* out_len);

Term store_real_run(Env e, Term* f, IoWork* w) {
  return hist_run(e, f[0], w, hist_path_real);
}

static void __attribute__((constructor)) store_real_use(void) {
  io_eff(CID_STORE_REAL, store_real_run, 0);
}
