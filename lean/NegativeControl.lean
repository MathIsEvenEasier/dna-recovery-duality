import Result

-- This file must be rejected. It is excluded from the successful proof build.
example : False := by
  exact True.intro
