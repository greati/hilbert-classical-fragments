import hilbert.wr.ad

namespace clfrags
    namespace hilbert
        namespace wr
            namespace ad
                
                theorem ad₂₆ {a b c : Prop} (h₁ : a) (h₂ : b) : ad a b c :=
                    have h₃ : ad (ad a b c) b a, from ad₂ h₂,
                    show ad a b c, from ad₁ h₁ h₃
                
                theorem ad₄' {a b c : Prop} (h₁ : a) : ad c a (ad c a (ad b a c)) :=
                    have h₂ : ad a a a, from ad₂₆ h₁ h₁,
                    have h₃ : ad (ad c a (ad c a (ad b a c))) a a, from ad₄ h₂,
                    show ad c a (ad c a (ad b a c)), from ad₁ h₁ h₃

                theorem ad₂₇ {a b c d e : Prop} (h₁ : ad (ad a b c) d e) : ad (ad a d e) b c :=
                    have h₂ : (ad a d e) or (ad a b c), from ad₁₀ h₁,
                    have h₃ : (ad a b c) or (ad a d e), from ad₁₃ h₂,
                    show ad (ad a d e) b c, from ad₁₁ h₃
            
                theorem ad₆' {a b : Prop} (h₁ : a) : a or b := 
                    ad₆ h₁
                
                theorem ad₁_ad {a b c d e : Prop} (h₁ : ad c d e) (h₂ : ad (ad a b c) d e) :
                    ad a d e := 
                    have h₃ : (ad (ad a b c) d e) → ((ad a d e) or (ad a b c)), from ad₁₀,
                    have h₄ : ad a d e → ad a d e, from R,
                    have h₅ : ad c d e → ad a b c → ad a d e, from ad₉,
                    have h₆ : ad c d e → ad a d e → ad a d e, from M₁ h₄,
                    have h₇ : ad c d e → ((ad a d e) or (ad a b c)) → ad a d e, from δ_or₂ h₆ h₅,
                    have h₈ : ad c d e → (ad (ad a b c) d e) → ((ad a d e) or (ad a b c)), from M₁ h₃,
                    show ad a d e, from (T₂ h₈ h₇) h₁ h₂

                theorem ad₂_ad {a b c d e : Prop} (h₁ : ad a d e) : ad (ad (ad c a b) a c) d e := 
                    let b' := ad c a b in
                        have h₂ : (ad a d e) → (((ad c a c) or b') or ((ad c d e) or b')),
                            from (assume h, ad₂₀ $ ad₁₃ $ ad₂₀ $ ad₁₀ $ ad₈ $ ad₁₃ $ ad₆' h),
                        have h₃ : ((ad c a c) or b') → ((ad b' d e) or (ad b' a c)),
                            from (assume h, ad₁₃ $ ad₆' $ ad₁₁ h),
                        have h₄ : ((ad c d e) or b') → ((ad b' d e) or (ad b' a c)), 
                            from (assume h, ad₆' $ ad₁₁ h),
                        have h₅ : (((ad c a c) or b') or ((ad c d e) or b')) → ((ad b' d e) or (ad b' a c)), 
                            from δ_or₁ h₃ h₄,
                        have h₆ : ad a d e → ((ad b' d e) or (ad b' a c)), 
                            from T₁ h₂ h₅,
                        show ad (ad b' a c) d e, 
                            from ad₁₁ (h₆ h₁)

                theorem ad₃_ad {a b c d e f g h : Prop} (h₁ : ad (ad a b c) g h) :
                    ad (ad (ad (ad (ad f a d) a (ad e a d)) a (ad (ad f a e) a d)) b c) g h :=
                    let j := ad (ad f a d) a (ad e a d), k := ad (ad f a e) a d, i := ad j a k in
                        have h₂ : (ad (ad a b c) g h) → ((ad a g h) or (ad a b c)), 
                            from ad₁₀,
                        have h₃ : ad a g h → ad (ad i b c) g h,
                            from (assume h₃₁, ad₁₁ $ ad₆' $ ad₃ h₃₁),
                        have h₄ : ad a b c → ad (ad i b c) g h,
                            from (assume h₄₁, ad₆ $ ad₃ h₄₁),
                        have h₅ : ((ad a g h) or (ad a b c)) → ad (ad i b c) g h,
                            from (δ_or₁ h₃ h₄),
                        (T₁ h₂ h₅) h₁

                theorem ad₄_ad {a b c d e f g : Prop} (h₁ : ad (ad a b c) f g) :
                    ad (ad (ad d a (ad d a (ad e a d))) b c) f g := 
                    let h := ad d a (ad d a (ad e a d)) in
                        have h₂ : (ad (ad a b c) f g) → ((ad a f g) or (ad a b c)), 
                            from ad₁₀,
                        have h₃ : ad a f g → ad (ad h b c) f g,
                            from (assume h₃₁, ad₁₁ $ ad₆' $ ad₄ h₃₁),
                        have h₄ : ad a b c → ad (ad h b c) f g,
                            from (assume h₄₁, ad₆ $ ad₄ h₄₁),
                        have h₅ : ((ad a f g) or (ad a b c)) → ad (ad h b c) f g,
                            from δ_or₁ h₃ h₄,
                        (T₁ h₂ h₅) h₁

                theorem ad₅_ad {a b c d e : Prop} (h₁ : ad (ad a b c) d e) : ad (b or a) d e :=
                    have h₂ : ad (ad a b c) d e → ((ad a d e) or (ad a b c)), 
                        from ad₁₀,
                    have h₃ : (ad a d e) → (ad (b or a) d e), 
                        from (assume h, ad₈ $ ad₁₃ $ ad₆' h),
                    have h₄ : (ad a b c) → (ad (b or a) d e), 
                        from (assume h, ad₆ $ ad₅ h),
                    have h₅ : ((ad a d e) or (ad a b c)) → (ad (b or a) d e), 
                        from δ_or₁ h₃ h₄,
                    (T₁ h₂ h₅) h₁

                theorem ad₆_ad {a b c d e : Prop} (h₁ : ad a d e) : ad (ad a b c) d e := 
                    ad₁₁ $ ad₆' h₁

                theorem ad₇_ad {a b c d e f : Prop} (h₁ : ad (ad (c or d) a b) e f) : 
                    ad ((ad c a b) or (ad d a b)) e f := 
                    have h₂ : ad (ad (c or d) a b) e f → ((ad (c or d) e f) or (ad (c or d) a b)), 
                        from ad₁₀,
                    have h₃ : ad (c or d) e f → ((ad c e f) or (ad d e f)),
                        from ad₇,
                    have h₄ : ad c e f → ad ((ad c a b) or (ad d a b)) e f,
                        from (assume h, ad₈ $ ad₆' $ ad₁₁ $ ad₆' h),
                    have h₅ : ad d e f → ad ((ad c a b) or (ad d a b)) e f,
                        from (assume h, ad₈ $ ad₁₃ $ ad₆' $ ad₁₁ $ ad₆' h),
                    have h₆ : ((ad c e f) or (ad d e f)) → ad ((ad c a b) or (ad d a b)) e f,
                        from δ_or₁ h₄ h₅,
                    have h₇ : ad (c or d) e f → ad ((ad c a b) or (ad d a b)) e f,
                        from T₁ h₃ h₆,
                    have h₈ : ad (c or d) a b → ad ((ad c a b) or (ad d a b)) e f,
                        from (assume h, ad₆ $ ad₇ h),
                    have h₉ : ((ad (c or d) e f) or (ad (c or d) a b)) → ad ((ad c a b) or (ad d a b)) e f,
                        from δ_or₁ h₇ h₈,
                    (T₁ h₂ h₉) h₁
                        
                theorem ad₁₂_ad {a b c: Prop} (h₁ : ad (a or a) b c) : ad a b c := 
                    ad₁₂ $ ad₇ h₁

                theorem ad₁₃_ad {a b c d : Prop} (h₁ : ad (a or b) c d) : ad (b or a) c d :=
                    ad₈ $ ad₁₃ $ ad₇ h₁

                theorem ad₁₄_ad {a b c d e : Prop} (h₁ : ad (a or (b or c)) d e) : ad ((a or b) or c) d e :=
                    ad₈ $ ad₁₃ $ ad₂₂ $ ad₁₃ $ ad₁₄ $ ad₂₁ $ ad₇ h₁
 
                theorem ad₈' {a b c d e f : Prop} (h₁ : ad (ad c a b) e f) : ad (ad (c or d) a b) e f := 
                    have h₂ : (ad (ad c a b) e f) → ((ad c e f) or (ad c a b)), from ad₁₀,
                    have h₃ : (ad c e f) → (ad (ad (c or d) a b) e f), from (assume h, ad₂₇ $ ad₆ $ ad₆_ad h),
                    have h₄ : (ad c a b) → (ad (ad (c or d) a b) e f), from (assume h, ad₆ $ ad₆_ad h),
                    have h₅ : ((ad c e f) or (ad c a b)) → (ad (ad (c or d) a b) e f), from δ_or₁ h₃ h₄,
                    show ad (ad (c or d) a b) e f, from (T₁ h₂ h₅) h₁               

                theorem ad₈'' {a b c d e f : Prop} (h₁ : ad (ad (c or d) a b) e f) : ad (ad (d or c) a b) e f :=
                    have h₃₁ : (ad (ad (c or d) a b) e f) → ((ad (c or d) e f) or (ad (c or d) a b)),
                        from ad₁₀,
                    have h₃₂ : ad (c or d) e f → ad (ad (d or c) a b) e f,
                        from (assume h, ad₂₇ $ ad₆ $ ad₁₃_ad h),
                    have h₃₃ : ad (c or d) a b → ad (ad (d or c) a b) e f,
                        from (assume h, ad₆ $ ad₁₃_ad h),
                    have h₃₄ : ((ad (c or d) e f) or (ad (c or d) a b)) → ad (ad (d or c) a b) e f,
                        from δ_or₁ h₃₂ h₃₃,
                    (T₁ h₃₁ h₃₄) h₁
                
                theorem ad₈_ad {a b c d e f : Prop} (h₁ : ad ((ad c a b) or (ad d a b)) e f) : 
                    ad (ad (c or d) a b) e f := 
                    have h₂ : ad ((ad c a b) or (ad d a b)) e f → ((ad (ad c a b) e f) or (ad (ad d a b) e f)),
                        from ad₇,
                    have h₃ : ad (ad c a b) e f → ad (ad (c or d) a b) e f, 
                        from ad₈',
                    have h₄ : ad (ad d a b) e f → ad (ad (c or d) a b) e f, 
                        from (assume h, ad₈'' $ ad₈' h),
                    have h₅ : ((ad (ad c a b) e f) or (ad (ad d a b) e f)) → ad (ad (c or d) a b) e f,
                        from δ_or₁ h₃ h₄,
                    (T₁ h₂ h₅) h₁

                theorem ad₉_ad {a b c d e f g : Prop} (h₁ : ad (ad a b c) f g) (h₂ : ad (ad d e a) f g) : ad (ad d b c) f g :=
                    let g' := ad d f g, c' := ad d b c in
                        have h₃ : ad (ad a b c) f g → ((ad a f g) or (ad a b c)), 
                            from ad₁₀,
                        have h₄ : ad (ad d e a) f g → (g' or (ad d e a)), 
                            from ad₁₀,
                        have h₅ : ad a b c → ad d f g → (g' or c'), 
                            from M₁ ad₆',
                        have h₆ : ad a b c → ad d e a → (g' or c'), 
                            from (assume h, assume i, ad₁₃ $ ad₆' $ ad₉ h i),
                        have h₇ : ad a f g → ad d f g → (g' or c'), 
                            from M₁ ad₆',
                        have h₈ : ad a f g → ad d e a → (g' or c'), 
                            from (assume h, assume i, ad₆' $ ad₉ h i),
                        have h₉ : (g' or (ad d e a)) → ad a b c → (g' or c'),
                            from flip (δ_or₂ h₅ h₆),
                        have h₁₀ : (g' or (ad d e a)) → ad a f g  → (g' or c'),
                            from flip (δ_or₂ h₇ h₈),
                        have h₁₁ : (g' or (ad d e a)) → ((ad a f g) or (ad a b c)) → (g' or c'),
                            from δ_or₂ h₁₀ h₉,
                        have h₁₂ : (ad (ad a b c) f g) → (g' or (ad d e a)) → (g' or c'),
                            from flip (T₂ (M₁ h₃) h₁₁),
                        have h₁₃ : (ad (ad a b c) f g) → (ad (ad d e a) f g) → (g' or c'),
                            from T₂ (M₁ h₄) h₁₂,
                        ad₁₁ (h₁₃ h₁ h₂)

                theorem ad₁₀_ad {a b c d e f g : Prop} (h₁ : ad (ad (ad e d c) a b) f g) 
                    : ad ((ad e a b) or (ad e d c)) f g :=
                    have h₂ : ad (ad (ad e d c) a b) f g → ((ad (ad e d c) f g) or (ad (ad e d c) a b)), 
                        from ad₁₀,
                    have h₃ : ad (ad e d c) f g → ad ((ad e a b) or (ad e d c)) f g,
                        from (assume h, ad₈ $ ad₁₃ $ ad₆' h),
                    have h₄ : ad (ad e d c) a b → ad ((ad e a b) or (ad e d c)) f g,
                        from (assume h, ad₆ $ ad₁₀ h),
                    have h₅ : ((ad (ad e d c) f g) or (ad (ad e d c) a b)) → ad ((ad e a b) or (ad e d c)) f g,
                        from δ_or₁ h₃ h₄,
                    (T₁ h₂ h₅) h₁

                theorem ad₁₁_ad {a b c d e f g : Prop} (h₁ : ad ((ad e a b) or (ad e d c)) f g) 
                    : ad (ad (ad e d c) a b) f g :=
                    have h₂ : ad ((ad e a b) or (ad e d c)) f g → ((ad (ad e a b) f g) or (ad (ad e d c) f g)),
                        from ad₇, 
                    have h₃ : ad (ad e a b) f g → ((ad e f g) or (ad e a b)),
                        from ad₁₀,
                    have h₄ : ad e f g → ((ad e f g) or (ad e d c)), 
                        from ad₆',
                    have h₅ : ((ad e f g) or (ad e d c)) → ad (ad (ad e d c) a b) f g,
                        from (assume h, ad₁₁ $ ad₁₃ $ ad₁₀ $ ad₆ $ ad₁₁ h),
                    have h₆ : ad e f g → ad (ad (ad e d c) a b) f g,
                        from T₁ h₄ h₅,
                    have h₇ : ((ad e a b) or (ad e d c)) → ad (ad (ad e d c) a b) f g,
                        from (assume h, ad₆ $ ad₁₁ h),
                    have h₈ : ad e a b → ((ad e a b) or (ad e d c)), 
                        from ad₆',
                    have h₉ : ad e a b → ad (ad (ad e d c) a b) f g,
                        from T₁ h₈ h₇,
                    have h₁₀ : ((ad e f g) or (ad e a b)) → ad (ad (ad e d c) a b) f g,
                        from δ_or₁ h₆ h₉,
                    have h₁₁ : ad (ad e a b) f g → ad (ad (ad e d c) a b) f g,
                        from T₁ h₃ h₁₀,
                    have h₁₂ : ad (ad e d c) f g → ad (ad (ad e d c) a b) f g,
                        from (assume h, ad₂₇ $ ad₆ $ ad₁₁ $ ad₁₀ h),
                    have h₁₃ : ((ad (ad e a b) f g) or (ad (ad e d c) f g)) → ad (ad (ad e d c) a b) f g,
                        from δ_or₁ h₁₁ h₁₂,
                    (T₁ h₂ h₁₃) h₁
            end ad
        end wr
    end hilbert
end clfrags
