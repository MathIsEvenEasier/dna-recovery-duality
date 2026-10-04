import CodeResult

-- This control must fail and is excluded from the successful proof build.
example : False := by
  exact True.intro
