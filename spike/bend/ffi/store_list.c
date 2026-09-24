// The C side of `Store.list`. The adapter is `store_locate.c`'s; the compiler
// splices both into one program, so the declaration is enough.
#include <stdint.h>

typedef int32_t (*HistCall)(const char* in, size_t in_len, char** out, size_t* out_len);
static Term hist_run(Env e, Term arg, IoWork* w, HistCall call);

extern int32_t hist_store_list(const char* root, size_t root_len, char** out, size_t* out_len);

Term store_list_run(Env e, Term* f, IoWork* w) {
  return hist_run(e, f[0], w, hist_store_list);
}

static void __attribute__((constructor)) store_list_use(void) {
  io_eff(CID_STORE_LIST, store_list_run, 0);
}
