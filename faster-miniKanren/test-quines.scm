(define appendo
  (lambda (l s out)
    (conde
      ((== '() l) (== s out))
      ((fresh (a d res)
         (== (cons a d) l)
         (== (cons a res) out)
         (appendo d s res))))))




(define evalo
  (lambda (exp val)
    (eval-expo exp '() val)))

(define eval-expo
  (lambda (exp env val)
    (conde
      ((fresh (v)
         (== `(quote ,v) exp)
         (not-in-envo 'quote env)
         (absento 'closure v)
         (== v val)))
      ((fresh (a*)
         (== `(list . ,a*) exp)
         (not-in-envo 'list env)
         (absento 'closure a*)
         (proper-listo a* env val)))
      ((symbolo exp) (lookupo exp env val))
      ((fresh (rator rand x body env^ a)
         (== `(,rator ,rand) exp)
         (eval-expo rator env `(closure ,x ,body ,env^))
         (eval-expo rand env a)
         (eval-expo body `((,x . ,a) . ,env^) val)))
      ((fresh (x body)
         (== `(lambda (,x) ,body) exp)
         (symbolo x)
         (not-in-envo 'lambda env)
         (== `(closure ,x ,body ,env) val))))))

(define not-in-envo
  (lambda (x env)
    (conde
      ((fresh (y v rest)
         (== `((,y . ,v) . ,rest) env)
         (=/= y x)
         (not-in-envo x rest)))
      ((== '() env)))))

(define proper-listo
  (lambda (exp env val)
    (conde
      ((== '() exp)
       (== '() val))
      ((fresh (a d t-a t-d)
         (== `(,a . ,d) exp)
         (== `(,t-a . ,t-d) val)
         (eval-expo a env t-a)
         (proper-listo d env t-d))))))

(define lookupo
  (lambda (x env t)
    (fresh (rest y v)
      (== `((,y . ,v) . ,rest) env)
      (conde
        ((== y x) (== v t))
        ((=/= y x) (lookupo x rest t))))))

#!eof

(test "1 quine"
  (run 1 (q) (eval-expo q '() q))
  '((((lambda (_.0) (list _.0 (list 'quote _.0)))
    '(lambda (_.0) (list _.0 (list 'quote _.0))))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))))

 (test "2 quines"
   (run 2 (q) (eval-expo q '() q))
   '((((lambda (_.0) (list _.0 (list 'quote _.0)))
    '(lambda (_.0) (list _.0 (list 'quote _.0))))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))
  (((lambda (_.0)
      (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))
     '(lambda (_.0)
        (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1)
    (absento (closure _.2)))))

 (test "3 quines"
   (run 3 (q) (eval-expo q '() q))
   '((((lambda (_.0) (list _.0 (list 'quote _.0)))
    '(lambda (_.0) (list _.0 (list 'quote _.0))))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))
  (((lambda (_.0)
      (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))
     '(lambda (_.0)
        (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (((lambda (_.0)
      (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))
     '(lambda (_.0)
        (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0))))
    (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
    (sym _.0 _.1)
    (absento (closure _.2)))))

 (test "5 quines"
   (run 5 (q) (eval-expo q '() q))
   '((((lambda (_.0) (list _.0 (list 'quote _.0)))
    '(lambda (_.0) (list _.0 (list 'quote _.0))))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))
  (((lambda (_.0)
      (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))
     '(lambda (_.0)
        (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (((lambda (_.0)
      (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))
     '(lambda (_.0)
        (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0))))
    (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (((lambda (_.0)
      (list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
     '(list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
    (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
    (sym _.0))
  (((lambda (_.0)
      (list _.0 (list ((lambda (_.1) _.1) 'quote) _.0)))
     '(lambda (_.0)
        (list _.0 (list ((lambda (_.1) _.1) 'quote) _.0))))
    (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1))))

 (test "10 quines"
   (run 10 (q) (eval-expo q '() q))
   '((((lambda (_.0) (list _.0 (list 'quote _.0)))
    '(lambda (_.0) (list _.0 (list 'quote _.0))))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))
  (((lambda (_.0)
      (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))
     '(lambda (_.0)
        (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (((lambda (_.0)
      (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))
     '(lambda (_.0)
        (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0))))
    (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (((lambda (_.0)
      (list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
     '(list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
    (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
    (sym _.0))
  (((lambda (_.0)
      (list _.0 (list ((lambda (_.1) _.1) 'quote) _.0)))
     '(lambda (_.0)
        (list _.0 (list ((lambda (_.1) _.1) 'quote) _.0))))
    (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1))
  (((lambda (_.0)
      ((lambda (_.1) (list _.0 (list 'quote _.0))) '_.2))
     '(lambda (_.0)
        ((lambda (_.1) (list _.0 (list 'quote _.0))) '_.2)))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (((lambda (_.0)
      (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2)))
     '(lambda (_.0)
        (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2))))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (((lambda (_.0)
      (list _.0 (list 'quote ((lambda (_.1) _.0) '_.2))))
     '(lambda (_.0)
        (list _.0 (list 'quote ((lambda (_.1) _.0) '_.2)))))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (((lambda (_.0)
      ((lambda (_.1) (list _.1 (list 'quote _.1))) _.0))
     '(lambda (_.0)
        ((lambda (_.1) (list _.1 (list 'quote _.1))) _.0)))
    (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
    (sym _.0 _.1))
  (((lambda (_.0)
      (list _.0 ((lambda (_.1) (list 'quote _.1)) _.0)))
     '(lambda (_.0)
        (list _.0 ((lambda (_.1) (list 'quote _.1)) _.0))))
    (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
    (sym _.0 _.1))))

 (test "40 quines"
   (run 40 (q) (eval-expo q '() q))
   '((((lambda (_.0) (list _.0 (list 'quote _.0)))
    '(lambda (_.0) (list _.0 (list 'quote _.0))))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))
 (((lambda (_.0)
     (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))
    '(lambda (_.0)
       (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0)))
    '(lambda (_.0)
       (list _.0 (list ((lambda (_.1) 'quote) '_.2) _.0))))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
   (sym _.0 _.1)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
    '(list (list 'lambda '(_.0) _.0) (list 'quote _.0)))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))
 (((lambda (_.0)
     (list _.0 (list ((lambda (_.1) _.1) 'quote) _.0)))
    '(lambda (_.0)
       (list _.0 (list ((lambda (_.1) _.1) 'quote) _.0))))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1))
 (((lambda (_.0)
     ((lambda (_.1) (list _.0 (list 'quote _.0))) '_.2))
    '(lambda (_.0)
       ((lambda (_.1) (list _.0 (list 'quote _.0))) '_.2)))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2)))
    '(lambda (_.0)
       (list _.0 ((lambda (_.1) (list 'quote _.0)) '_.2))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list _.0 (list 'quote ((lambda (_.1) _.0) '_.2))))
    '(lambda (_.0)
       (list _.0 (list 'quote ((lambda (_.1) _.0) '_.2)))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1)
   (absento (closure _.2)))
 (((lambda (_.0)
     ((lambda (_.1) (list _.1 (list 'quote _.1))) _.0))
    '(lambda (_.0)
       ((lambda (_.1) (list _.1 (list 'quote _.1))) _.0)))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list _.0 ((lambda (_.1) (list 'quote _.1)) _.0)))
    '(lambda (_.0)
       (list _.0 ((lambda (_.1) (list 'quote _.1)) _.0))))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     ((lambda (_.1) (list _.0 (list _.1 _.0))) 'quote))
    '(lambda (_.0)
       ((lambda (_.1) (list _.0 (list _.1 _.0))) 'quote)))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list _.0 ((lambda (_.1) (list _.1 _.0)) 'quote)))
    '(lambda (_.0)
       (list _.0 ((lambda (_.1) (list _.1 _.0)) 'quote))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list _.0 (list 'quote ((lambda (_.1) _.1) _.0))))
    '(lambda (_.0)
       (list _.0 (list 'quote ((lambda (_.1) _.1) _.0)))))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       (list ((lambda (_.3) 'quote) '_.4) _.0)))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         (list ((lambda (_.3) 'quote) '_.4) _.0))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.3 closure)) ((_.3 quote)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2) (closure _.4)))
 (((lambda (_.0)
     (list ((lambda (_.1) _.1) _.0) (list 'quote _.0)))
    '(lambda (_.0)
       (list ((lambda (_.1) _.1) _.0) (list 'quote _.0))))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list _.0 (list 'quote ((lambda (_.1) _.0) _.0))))
    '(lambda (_.0)
       (list _.0 (list 'quote ((lambda (_.1) _.0) _.0)))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list _.0 ((lambda (_.1) (list 'quote _.0)) _.0)))
    '(lambda (_.0)
       (list _.0 ((lambda (_.1) (list 'quote _.0)) _.0))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     ((lambda (_.1) (list _.1 (list 'quote _.0))) _.0))
    '(lambda (_.0)
       ((lambda (_.1) (list _.1 (list 'quote _.0))) _.0)))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list _.0 (list ((lambda (_.1) 'quote) _.0) _.0)))
    '(lambda (_.0)
       (list _.0 (list ((lambda (_.1) 'quote) _.0) _.0))))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       (list ((lambda (_.3) _.3) 'quote) _.0)))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         (list ((lambda (_.3) _.3) 'quote) _.0))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.3 closure)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       ((lambda (_.3) (list 'quote _.0)) '_.4)))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         ((lambda (_.3) (list 'quote _.0)) '_.4))))
   (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.0 closure)) ((_.0 lambda))
        ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.3 closure))
        ((_.3 list)) ((_.3 quote)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2) (closure _.4)))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       (list 'quote ((lambda (_.3) _.0) '_.4))))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         (list 'quote ((lambda (_.3) _.0) '_.4)))))
   (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.0 closure)) ((_.0 lambda))
        ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.3 closure)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2) (closure _.4)))
 (((lambda (_.0)
     (list
       _.0
       (list
         ((lambda (_.1) 'quote) '_.2)
         ((lambda (_.3) _.0) '_.4))))
    '(lambda (_.0)
       (list
         _.0
         (list
           ((lambda (_.1) 'quote) '_.2)
           ((lambda (_.3) _.0) '_.4)))))
   (=/= ((_.0 _.3)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 quote)) ((_.3 closure)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2) (closure _.4)))
 (((lambda (_.0)
     ((lambda (_.1) (list _.0 (list 'quote _.1))) _.0))
    '(lambda (_.0)
       ((lambda (_.1) (list _.0 (list 'quote _.1))) _.0)))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list _.0 (list 'quote ((lambda (_.1) _.0) (list)))))
    '(lambda (_.0)
       (list _.0 (list 'quote ((lambda (_.1) _.0) (list))))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list
       (list 'lambda '(_.0) _.0)
       (list ((lambda (_.1) 'quote) '_.2) _.0)))
    '(list
       (list 'lambda '(_.0) _.0)
       (list ((lambda (_.1) 'quote) '_.2) _.0)))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
   (sym _.0 _.1)
   (absento (closure _.2)))
 (((lambda (_.0)
     ((lambda (_.1)
        (list ((lambda (_.2) _.0) '_.3) (list 'quote _.0)))
       '_.4))
    '(lambda (_.0)
       ((lambda (_.1)
          (list ((lambda (_.2) _.0) '_.3) (list 'quote _.0)))
         '_.4)))
   (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda))
        ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda))
        ((_.1 list)) ((_.1 quote)) ((_.2 closure)))
   (sym _.0 _.1 _.2)
   (absento (closure _.3) (closure _.4)))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       ((lambda (_.3) (list 'quote _.3)) _.0)))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         ((lambda (_.3) (list 'quote _.3)) _.0))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.3 closure)) ((_.3 list))
        ((_.3 quote)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       ((lambda (_.3) (list _.3 _.0)) 'quote)))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         ((lambda (_.3) (list _.3 _.0)) 'quote))))
   (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.0 closure)) ((_.0 lambda))
        ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.3 closure))
        ((_.3 list)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       (list 'quote ((lambda (_.3) _.3) _.0))))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         (list 'quote ((lambda (_.3) _.3) _.0)))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.3 closure)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list _.0 ((lambda (_.1) (list 'quote _.0)) (list))))
    '(lambda (_.0)
       (list _.0 ((lambda (_.1) (list 'quote _.0)) (list)))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list
       _.0
       (list
         ((lambda (_.1) 'quote) '_.2)
         ((lambda (_.3) _.3) _.0))))
    '(lambda (_.0)
       (list
         _.0
         (list
           ((lambda (_.1) 'quote) '_.2)
           ((lambda (_.3) _.3) _.0)))))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 quote)) ((_.3 closure)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2)))
 (((lambda (_.0)
     ((lambda (_.1) (list _.0 (list 'quote _.0))) (list)))
    '(lambda (_.0)
       ((lambda (_.1) (list _.0 (list 'quote _.0))) (list))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list ((lambda (_.1) _.0) _.0) (list 'quote _.0)))
    '(lambda (_.0)
       (list ((lambda (_.1) _.0) _.0) (list 'quote _.0))))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list
       (list 'lambda '(_.0) _.0)
       (list ((lambda (_.1) _.1) 'quote) _.0)))
    '(list
       (list 'lambda '(_.0) _.0)
       (list ((lambda (_.1) _.1) 'quote) _.0)))
   (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)))
   (sym _.0 _.1))
 (((lambda (_.0)
     ((lambda (_.1) (list _.0 (list 'quote _.0))) _.0))
    '(lambda (_.0)
       ((lambda (_.1) (list _.0 (list 'quote _.0))) _.0)))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1))
 (((lambda (_.0)
     (list
       (list 'lambda '(_.0) _.0)
       ((lambda (_.1) (list 'quote _.0)) '_.2)))
    '(list
       (list 'lambda '(_.0) _.0)
       ((lambda (_.1) (list 'quote _.0)) '_.2)))
   (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
        ((_.0 quote)) ((_.1 closure)) ((_.1 list)) ((_.1 quote)))
   (sym _.0 _.1)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       (list 'quote ((lambda (_.3) _.0) _.0))))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         (list 'quote ((lambda (_.3) _.0) _.0)))))
   (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.0 closure)) ((_.0 lambda))
        ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.3 closure)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2)))
 (((lambda (_.0)
     (list
       ((lambda (_.1) _.0) '_.2)
       ((lambda (_.3) (list 'quote _.0)) _.0)))
    '(lambda (_.0)
       (list
         ((lambda (_.1) _.0) '_.2)
         ((lambda (_.3) (list 'quote _.0)) _.0))))
   (=/= ((_.0 _.1)) ((_.0 _.3)) ((_.0 closure)) ((_.0 lambda))
        ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.3 closure))
        ((_.3 list)) ((_.3 quote)))
   (sym _.0 _.1 _.3)
   (absento (closure _.2)))
 (((lambda (_.0)
     ((lambda (_.1)
        (list ((lambda (_.2) _.0) '_.3) (list _.1 _.0)))
       'quote))
    '(lambda (_.0)
       ((lambda (_.1)
          (list ((lambda (_.2) _.0) '_.3) (list _.1 _.0)))
         'quote)))
   (=/= ((_.0 _.1)) ((_.0 _.2)) ((_.0 closure)) ((_.0 lambda))
        ((_.0 list)) ((_.0 quote)) ((_.1 closure)) ((_.1 lambda))
        ((_.1 list)) ((_.1 quote)) ((_.2 closure)))
   (sym _.0 _.1 _.2)
   (absento (closure _.3)))))

(test "2 twines"
  (run 2 (x) (fresh (p q)
	       (=/= p q)
	       (eval-expo p '() q)
	       (eval-expo q '() p)
	       (== `(,p ,q) x)))
  '((('((lambda (_.0)
       (list 'quote (list _.0 (list 'quote _.0))))
      '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0)))))
    ((lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))
      '(lambda (_.0) (list 'quote (list _.0 (list 'quote _.0))))))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))
  (('((lambda (_.0)
        (list
          'quote
          (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))
       '(lambda (_.0)
          (list
            'quote
            (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))))
     ((lambda (_.0)
        (list
          'quote
          (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))
       '(lambda (_.0)
          (list
            'quote
            (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1)
    (absento (closure _.2)))))

(test "4 thrines"
  (run 4 (x)
    (fresh (p q r)
      (=/= p q)
      (=/= q r)
      (=/= r p)
      (eval-expo p '() q)
      (eval-expo q '() r)
      (eval-expo r '() p)
      (== `(,p ,q ,r) x)))
  '(((''((lambda (_.0)
        (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
       '(lambda (_.0)
          (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
    '((lambda (_.0)
        (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
       '(lambda (_.0)
          (list 'quote (list 'quote (list _.0 (list 'quote _.0))))))
    ((lambda (_.0)
       (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))
      '(lambda (_.0)
         (list 'quote (list 'quote (list _.0 (list 'quote _.0)))))))
   (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
   (sym _.0))
  ((''((lambda (_.0)
         (list
           'quote
           (list
             'quote
             (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))))
        '(lambda (_.0)
           (list
             'quote
             (list
               'quote
               (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))))
     '((lambda (_.0)
         (list
           'quote
           (list
             'quote
             (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))))
        '(lambda (_.0)
           (list
             'quote
             (list
               'quote
               (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0))))))
     ((lambda (_.0)
        (list
          'quote
          (list
            'quote
            (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))))
       '(lambda (_.0)
          (list
            'quote
            (list
              'quote
              (list ((lambda (_.1) _.0) '_.2) (list 'quote _.0)))))))
    (=/= ((_.0 _.1)) ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)))
    (sym _.0 _.1)
    (absento (closure _.2)))
  (('(list
       '(lambda (_.0)
          (list
            'quote
            (list 'list _.0 (list 'quote (list 'quote _.0)))))
       '''(lambda (_.0)
            (list
              'quote
              (list 'list _.0 (list 'quote (list 'quote _.0))))))
     (list
       '(lambda (_.0)
          (list
            'quote
            (list 'list _.0 (list 'quote (list 'quote _.0)))))
       '''(lambda (_.0)
            (list
              'quote
              (list 'list _.0 (list 'quote (list 'quote _.0))))))
     ((lambda (_.0)
        (list
          'quote
          (list 'list _.0 (list 'quote (list 'quote _.0)))))
       ''(lambda (_.0)
           (list
             'quote
             (list 'list _.0 (list 'quote (list 'quote _.0)))))))
    (=/= ((_.0 closure)) ((_.0 list)) ((_.0 quote)))
    (sym _.0))
  ((''((lambda (_.0)
         (list
           ((lambda (_.1) 'quote) '_.2)
           (list 'quote (list _.0 (list 'quote _.0)))))
        '(lambda (_.0)
           (list
             ((lambda (_.1) 'quote) '_.2)
             (list 'quote (list _.0 (list 'quote _.0))))))
     '((lambda (_.0)
         (list
           ((lambda (_.1) 'quote) '_.2)
           (list 'quote (list _.0 (list 'quote _.0)))))
        '(lambda (_.0)
           (list
             ((lambda (_.1) 'quote) '_.2)
             (list 'quote (list _.0 (list 'quote _.0))))))
     ((lambda (_.0)
        (list
          ((lambda (_.1) 'quote) '_.2)
          (list 'quote (list _.0 (list 'quote _.0)))))
       '(lambda (_.0)
          (list
            ((lambda (_.1) 'quote) '_.2)
            (list 'quote (list _.0 (list 'quote _.0)))))))
    (=/= ((_.0 closure)) ((_.0 lambda)) ((_.0 list))
         ((_.0 quote)) ((_.1 closure)) ((_.1 quote)))
    (sym _.0 _.1)
    (absento (closure _.2)))))
