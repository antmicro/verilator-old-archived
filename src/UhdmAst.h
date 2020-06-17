#ifndef _UHDM_AST_H_
#define _UHDM_AST_H_ 1

#include <vector>

#include "headers/uhdm.h"

#include "V3Ast.h"

namespace UhdmAst {

  // Visits single VPI object and creates proper AST node
  AstNode* visit_object (vpiHandle obj_h,
        std::set<const UHDM::BaseClass*> visited,
        std::map<std::string, AstNodeModule*>* top_nodes);

  // Visits all VPI design objects and returns created ASTs
  std::vector<AstNodeModule*> visit_designs (const std::vector<vpiHandle>& designs,
                                             std::ostream& coverage_report_stream);
}
#endif  // Guard
