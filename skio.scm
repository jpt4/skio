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

;;irreducible expressions
(define (irredexo i)
  (fresh (a b)
   (conde
    [(varo i)]
    [(combo i)]
    [(== `(K ,a) i) (irredexo a)]
    [(== `(S ,a) i) (irredexo a)]
    [(== `((S ,a) ,b) i) (irredexo a) (irredexo b)]
)))

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
(define (skio-aux i o)
  (fresh (a b resa resb res)
   (conde
    [(irredexo i) (== i o)]
    [(conde
      [(io i res) (skio-aux res o)]
      [(ko i res) (skio-aux res o)]
      [(so i res) (skio-aux res o)]
      [(== `(,a ,b) i) (skio-aux a resa) (skio-aux b resb)
       (== `(,resa ,resb) res) (=/= i res) (skio-aux res o)]
      [(== `(,a ,b) i) (skio-aux a resa) (skio-aux b resb)
       (== `(,resa ,resb) res) (== i res) (== i o)]
      )])))

;;Forward interpreter
(define (skio-fwd i d o)
  (fresh (a b c e f g resa resb resd resad resbd res exp diag)
   (conde
    [(== `(,a (,a ,b)) d) (== i a) (== i o) 
     #;(== `(stop i=,i a=,a b=,b d=,d) o)]
    [(conde
;    [(== '() i) (== i o)]
      [(combo i) #;(== `(,i ,d) resd) #;(skio-diag i resd o) (== i o)]
      [(varo i) #;(== `(,i ,d) resd) #;(skio-diag i resd o) (== i o)]
      [(io i res) (== `(,res ,d) resd) (skio-fwd res resd o) 
       #;(skio-diag res resd diag)
       #;(== `(so-lax i=,i res=,res d=,d resd=,resd diag=,diag) o)]
      [(ko i res) (== `(,res ,d) resd) (skio-fwd res resd o) 
       #;(skio-diag res resd diag)
       #;(== `(so-lax i=,i res=,res d=,d resd=,resd diag=,diag) o)]
      [(so i res) (== `(,res ,d) resd) (skio-fwd res resd o) 
       #;(skio-diag res resd diag)
       #;(== `(so-lax i=,i res=,res d=,d resd=,resd diag=,diag) o)]
      [(== `(,a ,b) i) (== `(,e (,f ,g)) d) (=/= e f) 
       (skio-fwd a d resa) (skio-fwd b d resb) 
       (== `(,resa ,resb) res) (== `(,res ,d) resd) 
       (skio-fwd res resd o)
       #;(skio-fwd res resd diag)
       #;(== `(pair i=,i a=,a b=,b e=,e f=,f g=,g resa=,resa resb=,resb res=,res resd=,resd d=,d diag=,diag) o)]
#;      [(== `((,a ,b) ,c) i)
       (skio-diag b res) (skio-diag `((,a ,res) ,c) o)]
#;      [(== `(,a (,b ,c)) i) 
       (skio-diag b res) (skio-diag `(,a (,b ,c)) o)]
    )])))

;;interpreter interface
(define (skio i o)
  (fresh (a)
   (laso i a) (skio-aux a o)))

;;Diagnostics instrumented interpreter core
(define (skio-diag i d o)
  (fresh (a b c resa resb resd resad resbd res exp diag)
   (conde
    [(== `(,a (,a ,b)) d) (== i a) (== i o) 
     #;(== `(stop i=,i a=,a b=,b d=,d) o)]
    [(conde
;    [(== '() i) (== i o)]
      [(combo i) (== `(,i ,d) resd) (skio-diag i resd o)]
      [(varo i) (== `(,i ,d) resd) (skio-diag i resd o)]
      [(io i res) (== `(,res ,d) resd) (skio-diag res resd o) 
       #;(skio-diag res resd diag)
       #;(== `(so-lax i=,i res=,res d=,d resd=,resd diag=,diag) o)]
      [(ko i res) (== `(,res ,d) resd) (skio-diag res resd o) 
       #;(skio-diag res resd diag)
       #;(== `(so-lax i=,i res=,res d=,d resd=,resd diag=,diag) o)]
      [(so i res) (== `(,res ,d) resd) (skio-diag res resd o) 
       #;(skio-diag res resd diag)
       #;(== `(so-lax i=,i res=,res d=,d resd=,resd diag=,diag) o)]
      [(== `(,a ,b) i) (skio-diag a d resa) (skio-diag b d resb) 
       (== `(,resa ,resb) res) (== `(,res ,d) resd) (skio-diag res resd o)
       #;(skio-diag res resd diag)
       #;(== `(pair i=,i a=,a b=,b resa=,resa resb=,resb res=,res resd=,resd d=,d diag=,diag) o)]
#;      [(== `((,a ,b) ,c) i)
       (skio-diag b res) (skio-diag `((,a ,res) ,c) o)]
#;      [(== `(,a (,b ,c)) i) 
       (skio-diag b res) (skio-diag `(,a (,b ,c)) o)]
    )])))

;;expose trace in single run
(define (strict-skio-dt i d t o)
  (fresh (a b c resa resb resd resad resbd res exp diag)
         (conde
          [(== `(,a (,a ,b)) d) (== i a) (== d t) (== i o)
           #;(== `(stop i=,i a=,a b=,b d=,d t=,t) o)]
          [(conde
           ;    [(== '() i) (== i o)]
            [(combo i) (== `(,i ,d) resd) (strict-skio i resd t o)]
            [(varo i) (== `(,i ,d) resd) (strict-skio i resd t o)]
            [(strict-io i res) (== `(,res ,d) resd) (strict-skio res resd t o)
             #;(strict-skio res resd t diag)
             #;(== `(so i=,i res=,res d=,d resd=,resd t=,t diag=,diag) o)]
            [(strict-ko i res) (== `(,res ,d) resd) #;(strict-skio res resd t o)
             (strict-skio res resd t diag)
             (== `(so i=,i res=,res d=,d resd=,resd t=,t diag=,diag) o)]
            [(strict-so i res) (== `(,res ,d) resd) (strict-skio res resd t o)
             #;(strict-skio res resd t diag)
             #;(== `(so i=,i res=,res d=,d resd=,resd t=,t diag=,diag) o)]
            [(== `(,a ,b) i) (strict-skio a d t resa) (strict-skio b d t resb)
             (== `(,resa ,resb) res) (== `(,res ,d) resd) #;(strict-skio res resd t o)
             #;(strict-skio res resd t diag)
             (== `(pair i=,i a=,a b=,b resa=,resa resb=,resb res=,res resd=,resd d=,d t=,t diag=,diag) o)]
            #;      [(== `((,a ,b) ,c) i)
            (strict-skio b res) (strict-skio `((,a ,res) ,c) o)]
            #;      [(== `(,a (,b ,c)) i) 
            (strict-skio b res) (strict-skio `(,a (,b ,c)) o)]
            )])))
