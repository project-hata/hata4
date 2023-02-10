import Lake
open Lake DSL

package «hata» {
  -- add any package configuration options here
}

@[default_target]
lean_exe «HataMain» {
  -- configuration options go here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- @[default_target]
lean_lib «Hata» {
  -- add any library configuration options here
}
