;;skio.scm
;;utc20170530
;;jpt4
;;Relational SKI combinator calculus interpreter in miniKanren
;;Chez Scheme v9.4-1

(load "miniKanren-with-symbolic-constraints/mk.scm")

;;the universe of variables
(define (varo i)
  (conde
   [(symbolo i)
    (=/= 'I i) (=/= 'K i) (=/= 'S i)]))
;;and combinators
(define (combo i)
  (conde
   [(== 'I i)]
   [(== 'K i)]
   [(== 'S i)]))
;;terms thereof
(define (termo i)
  (conde
   [(varo i)]
   [(combo i)]
   [(fresh (a d)
     (== `(,a ,d) i)
     (termo a) (termo d))]))

;;coerce left association in expressions
(define (laso i o)
  (conde
   [(termo i) (== i o)]
   [(fresh (a b resa resb)
     (== `(,a ,b) i) 
     (laso a resa) (laso b resb) (== `(,resa ,resb) o))]
   [(fresh (a b c resa resb resc)
     (== `(,a ,b ,c) i) 
     (laso a resa) (laso b resb) (laso c resc)
     (== `((,resa ,resb) ,resc) o))]
   [(fresh (a b c resa resb resc)
     (== `(,a ,b . ,c) i) (=/= '() c)
     (laso a resa) (laso b resb) (laso `((,resa ,resb) . ,c) o)
     )]
   ))

;;combinator reductions
(define (io i o)
  (fresh (x)
   (conde
    [(== `(I ,x) i) (== x o)])))
(define (ko i o)
  (fresh (x y)
   (conde
    [(== `((K ,x) ,y) i) (== x o)])))
(define (so i o)
  (fresh (x y z)
   (conde
    [(== `(((S ,x) ,y) ,z) i)  (== `((,x ,z) (,y ,z)) o)])))

;;core interpreter
(define (skio-core i t o)
  (fresh (a b c d e t0 t1 t2 resa resb rest res diag)
   (conde
    [(== `(,a (,a ,b)) t) (== i a) (== i o)]
    [(== `(,t2 (,t1 ,t0)) t) (=/= t2 t1)
     (conde
      [(combo i) (== i o)]
      [(varo i) (== i o)]
      [(io i res) (== `(,res ,t) rest) (skio-core res rest o)]
      [(ko i res) (== `(,res ,t) rest) (skio-core res rest o)]
      [(so i res) (== `(,res ,t) rest) (skio-core res rest o)]
      [(== `(,a ,b) i) 
       (skio-core a t resa) (skio-core b t resb)
       (== `(,resa ,resb) res) (== `(,res ,t) rest)
       (skio-core res rest o)]
      )])))

;;interpreter interfaces - note, contaminates mK relational logic with Scheme
;input evaluation (forward interpretation)
(define (skio exp)
  (let* ([t0 (gensym)] [t1 (gensym)] [t2 (gensym)]
         [init (list t2 (list t1 t0))])
    (run 1 (q) (fresh (i)
                (laso exp i) (skio-core i init q)))))

;input synthesis (reverse interpretation) - no laso preprocessing
(define (skio-syn exp num)
  (let* ([t0 (gensym)] [t1 (gensym)] [t2 (gensym)]
         [init (list t2 (list t1 t0))])
    (run num (q) (skio-core q init exp))))

;;alternative interpreter, does better at synthesis than evaluation
(define (skio-alt i o)
  (fresh (a b resa resb res)
   (conde
    [(irredexo i) (== i o)]
    [(conde
      [(io i res) (skio-alt res o)]
      [(ko i res) (skio-alt res o)]
      [(so i res) (skio-alt res o)]
      [(== `(,a ,b) i) (skio-alt a resa) (skio-alt b resb)
       (== `(,resa ,resb) res) (=/= i res) (skio-alt res o)]
      [(== `(,a ,b) i) (skio-alt a resa) (skio-alt b resb)
       (== `(,resa ,resb) res) (== i res) (== i o)]
      )])))

;;irreducible expressions for skio-alt
(define (irredexo i)
  (fresh (a b)
         (conde
          [(varo i)]
          [(combo i)]
          [(== `(K ,a) i) (irredexo a)]
          [(== `(S ,a) i) (irredexo a)]
          [(== `((S ,a) ,b) i) (irredexo a) (irredexo b)]
          )))

;;;UNDER CONSTRUCTION FROM THIS POINT ONWARDS
;;Diagnostics instrumented interpreter core
(define (skio-core-diag i t o)
  (fresh (a b c d e t0 t1 t2 resa resb rest res diag)
   (conde
    [(== `(,a (,a ,b)) t) (== i a) (== i o) 
     #;(== `(stop i=,i a=,a b=,b t=,t) o)]
    [(== `(,t2 (,t1 ,t0)) t) (=/= t2 t1)
     #;(== `(go i=,i t=,t t2=,t2 t1=,t1 t0=,t0) o)
     (conde
      [(combo i) (== i o) 
       #;(== `(combo i=,i) o)]
      [(varo i) (== i o)
       #;(== `(varo i=,i) o)]
      [(io i res) (== `(,res ,t) rest) (skio-core-diag res rest o) 
       #;(skio-core-diag res rest diag)
       #;(== `(io i=,i res=,res t=,t rest=,rest diag=,diag) o)]
      [(ko i res) (== `(,res ,t) rest) (skio-core-diag res rest o) 
       #;(skio-core-diag res rest diag)
       #;(== `(ko i=,i res=,res t=,t rest=,rest diag=,diag) o)]
      [(so i res) (== `(,res ,t) rest) (skio-core-diag res rest o) 
       #;(skio-core-diag res rest diag)
       #;(== `(so i=,i res=,res t=,t rest=,rest diag=,diag) o)]
      [(== `(,a ,b) i) 
       (skio-core-diag a t resa) (skio-core-diag b t resb) 
       (== `(,resa ,resb) res) (== `(,res ,t) rest) 
       (skio-core-diag res rest o)
       #;(skio-core-diag res rest diag)
       #;(== `(pair i=,i a=,a b=,b t=,t resa=,resa resb=,resb res=,res 
       rest=,rest diag=,diag) o)]
      )])))

;;expose trace in single run
#;(define (strict-skio-dt i d t o)
  (fresh (a b c resa resb rest resad resbd res exp diag)
         (conde
          [(== `(,a (,a ,b)) d) (== i a) (== d t) (== i o)
           #;(== `(stop i=,i a=,a b=,b t=,t t=,t) o)]
          [(conde
           ;    [(== '() i) (== i o)]
            [(combo i) (== `(,i ,t) rest) (strict-skio i rest t o)]
            [(varo i) (== `(,i ,t) rest) (strict-skio i rest t o)]
            [(strict-io i res) (== `(,res ,t) rest) (strict-skio res rest t o)
             #;(strict-skio res rest t diag)
             #;(== `(so i=,i res=,res t=,t rest=,rest t=,t diag=,diag) o)]
            [(strict-ko i res) (== `(,res ,t) rest) #;(strict-skio res rest t o)
             (strict-skio res rest t diag)
             (== `(so i=,i res=,res t=,t rest=,rest t=,t diag=,diag) o)]
            [(strict-so i res) (== `(,res ,t) rest) (strict-skio res rest t o)
             #;(strict-skio res rest t diag)
             #;(== `(so i=,i res=,res t=,t rest=,rest t=,t diag=,diag) o)]
            [(== `(,a ,b) i) (strict-skio a d t resa) (strict-skio b d t resb)
             (== `(,resa ,resb) res) (== `(,res ,t) rest) #;(strict-skio res rest t o)
             #;(strict-skio res rest t diag)
             (== `(pair i=,i a=,a b=,b resa=,resa resb=,resb res=,res rest=,rest t=,t t=,t diag=,diag) o)]
            #;      [(== `((,a ,b) ,c) i)
            (strict-skio b res) (strict-skio `((,a ,res) ,c) o)]
            #;      [(== `(,a (,b ,c)) i) 
            (strict-skio b res) (strict-skio `(,a (,b ,c)) o)]
            )])))
