#ifndef _UHDM_AST_H_
#define _UHDM_AST_H_ 1

#include <string.h>

#include <iostream>
#include <map>
#include <string>
#include <vector>

#include "include/sv_vpi_user.h"
#include "include/vhpi_user.h"

#include "headers/uhdm_types.h"
#include "headers/vpi_uhdm.h"
#include "headers/uhdm.h"

#include "V3Ast.h"

namespace UhdmAst {
  AstNode* visit_object (vpiHandle obj_h);
  std::vector<AstNodeModule*> visit_designs (const std::vector<vpiHandle>& designs);
}
#endif  // Guard
