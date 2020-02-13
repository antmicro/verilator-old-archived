#ifndef _UHDM_AST_H_
#define _UHDM_AST_H_ 1

#include <vector>

#include "headers/uhdm.h"

#include "V3Ast.h"

namespace UhdmAst {
  AstNode* visit_object (vpiHandle obj_h);
  std::vector<AstNodeModule*> visit_designs (const std::vector<vpiHandle>& designs);
}
#endif  // Guard
