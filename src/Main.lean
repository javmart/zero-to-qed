import ZeroToQED

def main : IO UInt32 := do
  IO.println "From Zero to QED"
  IO.println "================"
  IO.println ""
  IO.println "Run 'just serve' to view the articles."
  IO.println "Run 'lake build' to compile all modules."
  IO.println "Run 'lake test' to execute tests."

  return 0
