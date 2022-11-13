(map map (list 
             (lambda (x) (+ x x)) 
             (lambda (x) (- x))
             (lambda (x) (* x x)))
       '((1 2.0) (3 4e0) (5 6e-1) ))


[ScmNumber (ScmReal 0.2); ScmNumber (ScmRational (2, 1));
 ScmNumber (ScmReal 0.6667); ScmNumber (ScmReal 0.2667);
 ScmNumber (ScmReal 1.)]


 ScmConst'
 (ScmVector
   [ScmNumber (ScmRational (1, 1)); ScmNumber (ScmRational (2, 1));
    ScmNumber (ScmRational (3, 1))])
[ScmNumber (ScmReal 0.2);
 ScmNumber (ScmRational (2, 1));
 ScmNumber (ScmReal 0.6667); ScmNumber (ScmReal 0.2667); 
 ScmNumber (ScmReal 1.)]

scan_ast [ScmApplic' (ScmVar' (VarFree "/"),
 [ScmApplic' (ScmVar' (VarFree "+"),
   [ScmConst' (ScmNumber (ScmReal 0.2));
    ScmApplic' (ScmVar' (VarFree "*"),
     [ScmConst' (ScmNumber (ScmRational (2, 1)));
      ScmApplic' (ScmVar' (VarFree "-"),
       [ScmConst' (ScmNumber (ScmReal 0.6667));
        ScmConst' (ScmNumber (ScmReal 0.2667))])])]);
  ScmApplic' (ScmVar' (VarFree "/"),
   [ScmConst' (ScmNumber (ScmReal 1.));
    ScmConst' (ScmNumber (ScmRational (2, 1)))])])]

  ((lambda s ((lambda s ((lambda s s) s)) s)) 'mary 'had 'a 'little 'lambda)