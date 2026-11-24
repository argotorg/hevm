// In-process bitwuzla for the wasm build, driven by hevm one SMT-LIB command at a time.
// Built with -fignore-exceptions, since wasi-sdk has no C++ exception support: a throw
// reaches __cxa_throw below, which reports it and aborts.
#include <bitwuzla/cpp/bitwuzla.h>
#include <bitwuzla/cpp/parser.h>

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <sstream>
#include <string>
#include <typeinfo>
#include <vector>

#include "parser/smt2/parser.h"

namespace {

struct Instance
{
  bitwuzla::TermManager tm;
  bitwuzla::Options options;
  std::ostringstream out;
  std::unique_ptr<bzla::parser::smt2::Parser> parser;
  std::string taken;
};

}  // namespace

extern "C" {

void*
__cxa_allocate_exception(size_t size) noexcept
{
  return std::malloc(size);
}

int __cxa_atexit(void (*)(void*), void*, void*);

// for thread_local destructors: with one thread, they can run at exit
int
__cxa_thread_atexit(void (*dtor)(void*), void* obj, void* dso)
{
  return __cxa_atexit(dtor, obj, dso);
}

[[noreturn]] void
__cxa_throw(void* obj, std::type_info* type, void (*)(void*))
{
  if (*type == typeid(bitwuzla::Exception) || *type == typeid(bitwuzla::Unsupported)
      || *type == typeid(bitwuzla::option::Exception)
      || *type == typeid(bitwuzla::parser::Exception))
    std::fprintf(stderr, "bitwuzla: %s\n",
                 static_cast<bitwuzla::Exception*>(obj)->msg().c_str());
  else
    std::fprintf(stderr, "uncaught C++ exception of type %s\n", type->name());
  std::fflush(nullptr);
  std::abort();
}

// args are bitwuzla command line options, e.g. "--produce-models"
void*
hevm_bitwuzla_new(const char** args, size_t nargs)
{
  Instance* s = new Instance();
  std::vector<std::string> opts;
  const std::string bv_format = "--bv-output-format=";
  for (size_t i = 0; i < nargs; i++)
  {
    std::string arg = args[i];
    // like bitwuzla's main, which has this option rather than the library
    if (arg.rfind(bv_format, 0) == 0)
      s->out << bitwuzla::set_bv_format(std::stoi(arg.substr(bv_format.size())));
    else
      opts.push_back(arg);
  }
  s->options.set(opts);
  s->parser.reset(new bzla::parser::smt2::Parser(s->tm, s->options, &s->out));
  return s;
}

void
hevm_bitwuzla_delete(void* p)
{
  delete static_cast<Instance*>(p);
}

// Runs the SMT-LIB commands in cmd. What the solver prints, or an (error ...) line
// if parsing fails, is kept for hevm_bitwuzla_output.
void
hevm_bitwuzla_command(void* p, const char* cmd, size_t len)
{
  Instance* s = static_cast<Instance*>(p);
  if (!s->parser->parse(std::string(cmd, len), false, false))
  {
    std::string msg = s->parser->error_msg();
    for (char& c : msg)
      if (c == '\n' || c == '"') c = ' ';
    s->out << "(error \"" << msg << "\")\n";
  }
}

// What the solver printed since the last call. Valid until the next call on this instance.
const char*
hevm_bitwuzla_output(void* p, size_t* len)
{
  Instance* s = static_cast<Instance*>(p);
  s->taken = s->out.str();
  s->out.str("");
  s->out.clear();
  *len = s->taken.size();
  return s->taken.data();
}

}
