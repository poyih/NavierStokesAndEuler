import NavierStokes

/-! Count the constants declared by each `NavierStokes.*` module, to confirm that the
aggregate modules `NavierStokes` and `NavierStokes.R3` declare nothing. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut total := 0
  let mut nsModules := 0
  let mut empty : Array Name := #[]
  for h : i in [0:env.header.moduleNames.size] do
    let name := env.header.moduleNames[i]
    if name == `NavierStokes || (`NavierStokes).isPrefixOf name then
      nsModules := nsModules + 1
      let n := env.header.moduleData[i]!.constNames.size
      total := total + n
      if n == 0 then empty := empty.push name
  IO.println s!"NavierStokes modules in environment: {nsModules}"
  IO.println s!"total constants declared by them: {total}"
  IO.println s!"modules declaring zero constants: {empty}"
