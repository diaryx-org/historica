// The C side of `Store.locate` and `Store.list`: copy the argument out of
// Bend's heap, hand it to Rust on a helper thread, and rebuild the answer on
// the event loop. `../RUNTIME.md` is the shape; `../ffi/src/lib.rs` the ABI.
//
// Both effects are one function apart, so the adapter is written once, here,
// and `store_list.c` — spliced into the same C file — declares it.

#include <stdint.h>

typedef int32_t (*HistCall)(const char* in, size_t in_len, char** out, size_t* out_len);

extern void hist_free(char* p, size_t len);

// `w->data` holds the argument going in and the answer coming out; `w->hand`
// carries the Rust function to the helper thread, which has no other scratch.
static void hist_call(IoWork* w) {
  char* out = NULL; size_t n = 0;
  w->code = (u32)((HistCall)w->hand)((const char*)w->data, w->size, &out, &n);
  free(w->data);
  w->data = out; w->size = n;
}

static Term hist_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, w->data) : io_done(e, io_str(e, w->data, w->size));
  hist_free(w->data, w->size);
  return r;
}

static Term hist_run(Env e, Term arg, IoWork* w, HistCall call) {
  u64 n; w->data = io_cstr(e, arg, &n); w->size = n;
  w->hand = (intptr_t)call;
  return io_work(w, hist_call, hist_pack);
}


extern int32_t hist_store_locate(const char* from, size_t from_len, char** out, size_t* out_len);

Term store_locate_run(Env e, Term* f, IoWork* w) {
  return hist_run(e, f[0], w, hist_store_locate);
}

static void __attribute__((constructor)) store_locate_use(void) {
  io_eff(CID_STORE_LOCATE, store_locate_run, 0);
}
