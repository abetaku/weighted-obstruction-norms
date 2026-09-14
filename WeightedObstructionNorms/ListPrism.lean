import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel

noncomputable section
namespace WeightedObstructionNorms
namespace ListPrism
variable {K L : Type*}

abbrev Chain (K : Type*) := List K →₀ ℝ

def atom (l : List K) : Chain K := Finsupp.single l 1

def cone (a : K) : Chain K →ₗ[ℝ] Chain K := Finsupp.lmapDomain ℝ ℝ (List.cons a)

def map (f : L → K) : Chain L →ₗ[ℝ] Chain K := Finsupp.lmapDomain ℝ ℝ (List.map f)

@[simp] lemma cone_atom (a : K) (l : List K) : cone a (atom l) = atom (a :: l) := by
  simp [cone, atom, Finsupp.lmapDomain_apply]

@[simp] lemma map_atom (f : L → K) (l : List L) : map f (atom l) = atom (l.map f) := by
  simp [map, atom, Finsupp.lmapDomain_apply]

def boundaryBasis : List K → Chain K
  | [] => 0
  | a :: l => atom l - cone a (boundaryBasis l)

def boundary : Chain K →ₗ[ℝ] Chain K := Finsupp.linearCombination ℝ boundaryBasis

@[simp] lemma boundary_atom (l : List K) : boundary (atom l) = boundaryBasis l := by
  simp [boundary, atom]

lemma boundary_cone (a : K) (c : Chain K) : boundary (cone a c) = c - cone a (boundary c) := by
  have h : boundary.comp (cone a) = LinearMap.id - (cone a).comp boundary := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp [boundaryBasis, map_smul]
  exact congrArg (fun f : Chain K →ₗ[ℝ] Chain K => f c) h

lemma map_cone (f : L → K) (a : L) (c : Chain L) : map f (cone a c) = cone (f a) (map f c) := by
  have h : (map f).comp (cone a) = (cone (f a)).comp (map f) := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp
  exact congrArg (fun F : Chain L →ₗ[ℝ] Chain K => F c) h

lemma boundary_map_basis (f : L → K) (l : List L) : boundaryBasis (l.map f) = map f (boundaryBasis l) := by
  induction l with
  | nil => simp [boundaryBasis]
  | cons a l ih => simp [boundaryBasis, ih, map_cone]

lemma boundary_map (f : L → K) (c : Chain L) : boundary (map f c) = map f (boundary c) := by
  have h : boundary.comp (map f) = (map f).comp boundary := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp [boundary_map_basis]
  exact congrArg (fun F : Chain L →ₗ[ℝ] Chain K => F c) h

/-- Recursive form of the usual prism triangulation. -/
def prismBasis (f g : L → K) : List L → Chain K
  | [] => 0
  | a :: l => cone (f a) (cone (g a) (atom (l.map g))) - cone (f a) (prismBasis f g l)

def prism (f g : L → K) : Chain L →ₗ[ℝ] Chain K := Finsupp.linearCombination ℝ (prismBasis f g)

@[simp] lemma prism_atom (f g : L → K) (l : List L) : prism f g (atom l) = prismBasis f g l := by
  simp [prism, atom]

lemma prism_cone (f g : L → K) (a : L) (c : Chain L) :
    prism f g (cone a c) = cone (f a) (cone (g a) (map g c)) - cone (f a) (prism f g c) := by
  have h : (prism f g).comp (cone a) =
      (cone (f a)).comp ((cone (g a)).comp (map g)) - (cone (f a)).comp (prism f g) := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp [prismBasis, smul_sub]
  exact congrArg (fun F : Chain L →ₗ[ℝ] Chain K => F c) h

lemma prism_identity_basis (f g : L → K) (l : List L) :
    boundary (prismBasis f g l) + prism f g (boundaryBasis l) = atom (l.map g) - atom (l.map f) := by
  induction l with
  | nil => simp [prismBasis, boundaryBasis]
  | cons a l ih =>
    simp only [prismBasis, boundaryBasis, map_sub, boundary_cone, prism_atom, prism_cone,
      List.map_cons, ← cone_atom, boundary_atom, boundary_map_basis]
    have hi := congrArg (cone (f a)) ih
    simp only [map_add, map_sub] at hi
    have hh := congrArg (fun z : Chain K => z - cone (f a) (atom (l.map g)) + cone (g a) (atom (l.map g))) hi
    convert hh using 1 <;> abel

/-- The augmented prism homotopy, valid for arbitrary selections f and g.
Repeated vertices are allowed at this stage. -/
theorem prism_identity (f g : L → K) (c : Chain L) :
    boundary (prism f g c) + prism f g (boundary c) = map g c - map f c := by
  have h : boundary.comp (prism f g) + (prism f g).comp boundary = map g - map f := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_smul, prism_atom, boundary_atom,
      ← smul_add, LinearMap.sub_apply, map_atom, ← smul_sub]
    rw [prism_identity_basis]
  exact congrArg (fun F : Chain L →ₗ[ℝ] Chain K => F c) h

lemma prism_naturality_basis {K' L' : Type*} (a : K → K') (b : L → L')
    (f g : L → K) (f' g' : L' → K') (hf : ∀ i, a (f i) = f' (b i))
    (hg : ∀ i, a (g i) = g' (b i)) (l : List L) :
    map a (prismBasis f g l) = prismBasis f' g' (l.map b) := by
  induction l with
  | nil => simp [prismBasis]
  | cons i l ih =>
    simp only [prismBasis, map_sub, map_cone, map_atom, List.map_cons, ih, hf, hg]
    congr 3
    rw [List.map_map, List.map_map]
    exact congrArg (fun k : L → K' => atom (l.map k)) (funext hg)

lemma prism_naturality {K' L' : Type*} (a : K → K') (b : L → L')
    (f g : L → K) (f' g' : L' → K') (hf : ∀ i, a (f i) = f' (b i))
    (hg : ∀ i, a (g i) = g' (b i)) (c : Chain L) :
    map a (prism f g c) = prism f' g' (map b c) := by
  have h : (map a).comp (prism f g) = (prism f' g').comp (map b) := by
    apply Finsupp.lhom_ext
    intro l r
    have hr : Finsupp.single l r = r • atom l := by simp [atom]
    rw [hr]
    simp only [LinearMap.comp_apply, map_smul, prism_atom, map_atom]
    rw [prism_naturality_basis a b f g f' g' hf hg]
  exact congrArg (fun F : Chain L →ₗ[ℝ] Chain K' => F c) h

end ListPrism
end WeightedObstructionNorms
