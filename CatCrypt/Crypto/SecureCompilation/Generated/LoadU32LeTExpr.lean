module

public import HaxLean.TExpr

@[expose] public section
/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Typed hax expression for `load_u32_le`

`loadU32LeTexpr` is the reducible `Hax.TExpr` literal of the ChaCha20-Poly1305
`load_u32_le` function, generated from `chacha20poly1305-hax/hax_frontend_export.json` by
hax-lean's `parseHaxFileWithTExpr` and `tPipelineFull`. `texprToThir` consumes it.
The file is generated; regenerate it rather than editing it by hand.
-/
def loadU32LeTexpr : Hax.TExpr :=
Hax.TExpr.mk
  (Hax.TExprKind.letBind
    "bytes"
    (Hax.TExpr.mk
      (Hax.TExprKind.var "bytes")
      (Hax.ImpType.ref (Hax.ImpType.array (Hax.ImpType.uint (Hax.IntWidth.w8)) 32) false))
    (Hax.TExpr.mk
      (Hax.TExprKind.letBind
        "off"
        (Hax.TExpr.mk (Hax.TExprKind.var "off") (Hax.ImpType.uint (Hax.IntWidth.wsize)))
        (Hax.TExpr.mk
          (Hax.TExprKind.app
            "BitOr#32"
            [Hax.TExpr.mk
               (Hax.TExprKind.app
                 "BitOr#32"
                 [Hax.TExpr.mk
                    (Hax.TExprKind.app
                      "BitOr#32"
                      [Hax.TExpr.mk
                         (Hax.TExprKind.app
                           "cast#32"
                           [Hax.TExpr.mk
                              (Hax.TExprKind.app
                                "index"
                                [Hax.TExpr.mk
                                   (Hax.TExprKind.var "bytes")
                                   (Hax.ImpType.ref (Hax.ImpType.array (Hax.ImpType.uint (Hax.IntWidth.w8)) 32) false),
                                 Hax.TExpr.mk (Hax.TExprKind.var "off") (Hax.ImpType.uint (Hax.IntWidth.wsize))])
                              (Hax.ImpType.uint (Hax.IntWidth.w8))])
                         (Hax.ImpType.uint (Hax.IntWidth.w32)),
                       Hax.TExpr.mk
                         (Hax.TExprKind.app
                           "Shl#32"
                           [Hax.TExpr.mk
                              (Hax.TExprKind.app
                                "cast#32"
                                [Hax.TExpr.mk
                                   (Hax.TExprKind.app
                                     "index"
                                     [Hax.TExpr.mk
                                        (Hax.TExprKind.var "bytes")
                                        (Hax.ImpType.ref
                                          (Hax.ImpType.array (Hax.ImpType.uint (Hax.IntWidth.w8)) 32)
                                          false),
                                      Hax.TExpr.mk
                                        (Hax.TExprKind.app
                                          "Add"
                                          [Hax.TExpr.mk
                                             (Hax.TExprKind.var "off")
                                             (Hax.ImpType.uint (Hax.IntWidth.wsize)),
                                           Hax.TExpr.mk
                                             (Hax.TExprKind.lit (Hax.ImpLit.int 1))
                                             (Hax.ImpType.uint (Hax.IntWidth.wsize))])
                                        (Hax.ImpType.uint (Hax.IntWidth.wsize))])
                                   (Hax.ImpType.uint (Hax.IntWidth.w8))])
                              (Hax.ImpType.uint (Hax.IntWidth.w32)),
                            Hax.TExpr.mk (Hax.TExprKind.lit (Hax.ImpLit.int 8)) (Hax.ImpType.sint (Hax.IntWidth.w32))])
                         (Hax.ImpType.uint (Hax.IntWidth.w32))])
                    (Hax.ImpType.uint (Hax.IntWidth.w32)),
                  Hax.TExpr.mk
                    (Hax.TExprKind.app
                      "Shl#32"
                      [Hax.TExpr.mk
                         (Hax.TExprKind.app
                           "cast#32"
                           [Hax.TExpr.mk
                              (Hax.TExprKind.app
                                "index"
                                [Hax.TExpr.mk
                                   (Hax.TExprKind.var "bytes")
                                   (Hax.ImpType.ref (Hax.ImpType.array (Hax.ImpType.uint (Hax.IntWidth.w8)) 32) false),
                                 Hax.TExpr.mk
                                   (Hax.TExprKind.app
                                     "Add"
                                     [Hax.TExpr.mk (Hax.TExprKind.var "off") (Hax.ImpType.uint (Hax.IntWidth.wsize)),
                                      Hax.TExpr.mk
                                        (Hax.TExprKind.lit (Hax.ImpLit.int 2))
                                        (Hax.ImpType.uint (Hax.IntWidth.wsize))])
                                   (Hax.ImpType.uint (Hax.IntWidth.wsize))])
                              (Hax.ImpType.uint (Hax.IntWidth.w8))])
                         (Hax.ImpType.uint (Hax.IntWidth.w32)),
                       Hax.TExpr.mk (Hax.TExprKind.lit (Hax.ImpLit.int 16)) (Hax.ImpType.sint (Hax.IntWidth.w32))])
                    (Hax.ImpType.uint (Hax.IntWidth.w32))])
               (Hax.ImpType.uint (Hax.IntWidth.w32)),
             Hax.TExpr.mk
               (Hax.TExprKind.app
                 "Shl#32"
                 [Hax.TExpr.mk
                    (Hax.TExprKind.app
                      "cast#32"
                      [Hax.TExpr.mk
                         (Hax.TExprKind.app
                           "index"
                           [Hax.TExpr.mk
                              (Hax.TExprKind.var "bytes")
                              (Hax.ImpType.ref (Hax.ImpType.array (Hax.ImpType.uint (Hax.IntWidth.w8)) 32) false),
                            Hax.TExpr.mk
                              (Hax.TExprKind.app
                                "Add"
                                [Hax.TExpr.mk (Hax.TExprKind.var "off") (Hax.ImpType.uint (Hax.IntWidth.wsize)),
                                 Hax.TExpr.mk
                                   (Hax.TExprKind.lit (Hax.ImpLit.int 3))
                                   (Hax.ImpType.uint (Hax.IntWidth.wsize))])
                              (Hax.ImpType.uint (Hax.IntWidth.wsize))])
                         (Hax.ImpType.uint (Hax.IntWidth.w8))])
                    (Hax.ImpType.uint (Hax.IntWidth.w32)),
                  Hax.TExpr.mk (Hax.TExprKind.lit (Hax.ImpLit.int 24)) (Hax.ImpType.sint (Hax.IntWidth.w32))])
               (Hax.ImpType.uint (Hax.IntWidth.w32))])
          (Hax.ImpType.uint (Hax.IntWidth.w32))))
      (Hax.ImpType.uint (Hax.IntWidth.w32))))
  (Hax.ImpType.uint (Hax.IntWidth.w32))
