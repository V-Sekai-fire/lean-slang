// FFI shim: compile emitted Slang → SPIR-V via libslang's modern API.
//
// libslang is built against GNU libstdc++, but the host Lean runtime is built
// against LLVM libc++/libc++abi. Loaded together the normal way, libc++abi
// shadows the __cxa_*/RTTI symbols libstdc++-built libslang relies on, and
// Slang's internal dynamic_cast (during core-module compilation) breaks. We
// therefore `dlmopen` libslang into a fresh link-map namespace (LM_ID_NEWLM),
// which loads it and all its deps fully isolated from the host's libc++, so its
// own libstdc++-based RTTI stays self-consistent. Only the C entry
// `slang_createGlobalSession` is dlsym'd; everything after is C++ vtable
// dispatch into libslang, which lives entirely in that namespace.
#include "slang.h"
#include "slang-com-ptr.h"
#include <dlfcn.h>
#include <cstdint>
#include <lean/lean.h>
using namespace slang;

typedef SlangResult (*CreateGlobalFn)(SlangInt, IGlobalSession**);

// Lean passes `String` as a boxed `lean_object*`; extract the C string with
// `lean_string_cstr`. Returns the SPIR-V byte size (>0) or a negative error
// code (int64_t = Lean's unboxed `Int64` FFI scalar).
extern "C" int64_t leanslang_spirv_size(b_lean_obj_arg srcObj, b_lean_obj_arg entryObj) {
  const char* src   = lean_string_cstr(srcObj);
  const char* entry = lean_string_cstr(entryObj);
  void* h = dlmopen(LM_ID_NEWLM, "libslang.so", RTLD_NOW);
  if (!h) return -10;
  auto createGlobal = (CreateGlobalFn)dlsym(h, "slang_createGlobalSession");
  if (!createGlobal) return -11;

  Slang::ComPtr<IGlobalSession> global;
  if (SLANG_FAILED(createGlobal(SLANG_API_VERSION, global.writeRef()))) return -1;

  TargetDesc target = {};
  target.format  = SLANG_SPIRV;
  target.profile = global->findProfile("spirv_1_5");
  SessionDesc sdesc = {};
  sdesc.targets = &target; sdesc.targetCount = 1;

  Slang::ComPtr<ISession> session;
  if (SLANG_FAILED(global->createSession(sdesc, session.writeRef()))) return -2;

  Slang::ComPtr<IBlob> diag;
  IModule* mod = session->loadModuleFromSourceString("m", "m.slang", src, diag.writeRef());
  if (!mod) return -3;
  Slang::ComPtr<IEntryPoint> ep;
  if (SLANG_FAILED(mod->findEntryPointByName(entry, ep.writeRef()))) return -4;
  IComponentType* comps[] = { mod, ep.get() };
  Slang::ComPtr<IComponentType> composed;
  if (SLANG_FAILED(session->createCompositeComponentType(comps, 2, composed.writeRef(), diag.writeRef()))) return -5;
  Slang::ComPtr<IBlob> spirv;
  if (SLANG_FAILED(composed->getEntryPointCode(0, 0, spirv.writeRef(), diag.writeRef()))) return -6;
  return (long)spirv->getBufferSize();
}
