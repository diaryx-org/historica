// The C side of `Store.move`. The adapter is `store_locate.c`'s; the
// compiler splices both into one program, so the declaration is enough.
#include <stdint.h>

typedef int32_t (*HistCall)(const char* in, size_t in_len, char** out, size_t* out_len);
static Term hist_run(Env e, Term arg, IoWork* w, HistCall call);

extern int32_t hist_folder_move(const char* query, size_t query_len, char** out, size_t* out_len);

Term store_move_run(Env e, Term* f, IoWork* w) {
  return hist_run(e, f[0], w, hist_folder_move);
}

static void __attribute__((constructor)) store_move_use(void) {
  io_eff(CID_STORE_MOVE, store_move_run, 0);
}
