// The C side of `Store.run`. The adapter is `store_locate.c`'s; the
// compiler splices both into one program, so the declaration is enough.
// What this program has printed is flushed first: the one run shares the
// standard streams, and what was said before it has to come before it.
#include <stdint.h>

typedef int32_t (*HistCall)(const char* in, size_t in_len, char** out, size_t* out_len);
static Term hist_run(Env e, Term arg, IoWork* w, HistCall call);

extern int32_t hist_process_run(const char* query, size_t query_len, char** out, size_t* out_len);

Term store_run_run(Env e, Term* f, IoWork* w) {
  fflush(stdout);
  return hist_run(e, f[0], w, hist_process_run);
}

static void __attribute__((constructor)) store_run_use(void) {
  io_eff(CID_STORE_RUN, store_run_run, 0);
}
