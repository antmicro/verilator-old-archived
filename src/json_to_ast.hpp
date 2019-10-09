#pragma once

#include "json.hpp"
#include "V3Ast.h"

#include <string>

namespace json_to_ast
{

void load(AstNetlist *design_root, const std::string &filepath);

} // namespace json_to_ast