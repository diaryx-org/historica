// The C side of `Store.mkdirs`. The adapter is `store_locate.c`'s; the
// compiler splices both into one program, so the declaration is enough.
#include <stdint.h>

typedef int32_t (*HistCall)(const char* in, size_t in_len, char** out, size_t* out_len);
static Term hist_run(Env e, Term arg, IoWork* w, HistCall call);

extern int32_t hist_dirs_make(const char* query, size_t query_len, char** out, size_t* out_len);

Term store_mkdirs_run(Env e, Term* f, IoWork* w) {
  return hist_run(e, f[0], w, hist_dirs_make);
}

static void __attribute__((constructor)) store_mkdirs_use(void) {
  io_eff(CID_STORE_MKDIRS, store_mkdirs_run, 0);
}
