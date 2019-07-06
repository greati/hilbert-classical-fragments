import hilbert.wr.or

open clfrags.hilbert.wr

namespace clfrags

    theorem ρ₁' {p q : Prop} (q₁ : q) : or p q :=
        have h₁ : or q p, from or.ρ₁ q₁,
        show or p q, from or.ρ₃ h₁

    theorem ρ₄' {p q r : Prop} (p₁ : or (or p q) r) : or p (or q r) :=
        have h₁ : or r (or p q), from or.ρ₃ p₁,
        have h₂ : or (or r p) q, from or.ρ₄ h₁,
        have h₃ : or q (or r p), from or.ρ₃ h₂,
        have h₄ : or (or q r) p, from or.ρ₄ h₃,
        show or p (or q r), from or.ρ₃ h₄

end clfrags
