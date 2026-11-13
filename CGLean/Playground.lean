module

public meta import ProofWidgets.Data.Svg
public meta import ProofWidgets.Component.HtmlDisplay
public meta import Mathlib.Algebra.Order.Ring.Rat
public meta import CGLean.Render.Region
public meta import CGLean.Render.Utils

public meta import CGLean.Geometry.Arrangement

meta section


open ProofWidgets Svg

def bigTri : Arrangement ℚ := {
  edges := [
    ((0, 0), []),
    ((0,2), [⟨(0,0), true, false⟩]),
    ((2,0), [⟨(0,2), true, false⟩, ⟨(0,0), false, true⟩])
  ]
}

def square : Arrangement ℚ := {
  edges := [
    ((0,0), []),
    ((0,1), [⟨(0,0), true, false⟩]),
    ((1,0), [⟨(0,0), false, true⟩]),
    ((1,1), [⟨(0,1), true, false⟩, ⟨(1,0), false, true⟩])
  ]
}

def t : Point ℚ := (3/4,3/4)

def frame : Frame where
  xmin   := -1
  ymin   := -1
  xSize  := 4
  width  := 400
  height := 400

#html (bigTri |> toSvg frame) ++ (square + t |> toSvg _) |>.toHtml
