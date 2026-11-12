module

public meta import ProofWidgets.Data.Svg
public meta import CGLean.Classes.Floatable

public meta section

open ProofWidgets Svg

variable {frame : Frame}

instance: Append (Svg frame) where
  -- TODO: what about index map?
  append s1 s2 := { elements := s1.elements ++ s2.elements }

