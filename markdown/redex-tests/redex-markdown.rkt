#lang racket
(require redex/reduction-semantics)

;; redex grammar for markdown
;; based on https://github.com/mfp/ocsiblog/blob/more-markdown-compat/simple_markup.ml

;; non-terminals have "$" prefix
(define-language MD
  ($md ($top ...))
  ($md+ ($top+ ...))
  ($top $words); $header $lst)
  ($top+ $words+); $header $lst)
;  ($header)
;  ($lst)
;  ($paras ($para $para ...))
;  ($para $words) ;(pre str str ...) (heading n $words) (quote $paras)
;         ;(ulst $paras $paras ...) (olst $paras $paras ...))
;  ($paras+ ($para+ $para+ ...))
;  ($para+ $words+)
  (n natural)
  ($words ($word ...))
  ($words+ ($word+ ...))
  ;; $word is for random generation; $word+ includes all possible words (eg refimg)
  ($word str (em str) (strong str) #;(struck $words)
         (code str) #;(anchor str) $link $img)
  ($word+ $word 
          (reflink desc id) (linkref id $url) (linkref id $url titl)
          (refimg desc id) (refimg id) (imgref id $url) (imgref id $url titl))
  (str (side-condition 
        string_1 
        (and (not (string=? (term string_1) ""))
             (andmap char-alphabetic? (string->list (term string_1))))))
  (str/lower (side-condition
              string_1
              (regexp-match #rx"^[a-z_0-9]+$" (term string_1))))
  ($link (inlink $url desc) (inlink $url desc titl) ; desc = between the </a>
         (reflink $url desc id) (reflink $url desc id titl))
  ($img (inimg $url desc) (inimg $url desc titl)    ; desc = alt text
        (refimg $url desc id) (refimg $url desc id titl)
        (refimg $url id)) 
  (desc str) (titl str)
  (id str/lower)
  ($url (url $url-scheme str $url-tld (str ...)) 
        (url $url-scheme $url-www str $url-tld (str ...))
        (url $url-scheme str str $url-tld (str ...)))
  ($url-tld "com" "org" "net")
  ($url-www "www")
  ($url-scheme "http" "ftp" "file" "telnet"))

(define-metafunction MD
  url->str : $url -> string
  [(url->str (url $url-scheme str $url-tld (str_1 ...)))
   ,(string-append (term $url-scheme) "://" (term str) "." (term $url-tld) "/" 
                   (string-join (term (str_1 ...)) "/"))]
  [(url->str (url $url-scheme $url-www str $url-tld (str_1 ...)))
   ,(string-append (term $url-scheme) "://" (term $url-www) "." (term str) "." 
                   (term $url-tld) "/" (string-join (term (str_1 ...)) "/"))]
  [(url->str (url $url-scheme str_1 str_2 $url-tld (str_3 ...)))
   ,(string-append (term $url-scheme) "://" (term str_1) "." (term str_2) "."
                   (term $url-tld) "/" (string-join (term (str_3 ...)) "/"))])
  

;; keep track of ref ids to make sure they are unique
(define ids null) ; list of symbols
;; returns fresh id as string
(define (frsh)
  (define x (symbol->string (variable-not-in ids 'x)))
  (add-to-ids! x)
  x)
(define (add-to-ids! str) (set! ids (cons (string->symbol str) ids)))
(define (seen-id? str) (member (string->symbol str) ids))

;; pre-process ----------------------------------------------------------------
;; pre-process a $md
;; - splits reflinks and refimgs
(define (pre m)
  (define-metafunction MD
    pre : $md+ $md+ -> $md+
  [(pre ($top+ ...) ()) ($top+ ...)] ;; done (dont need this one?)
  [(pre ($top+ ...) (())) ($top+ ...)] ;; done
  ;; reflink : no title
  [(pre ($top+_1 ... ($word+_1 ...)) 
        (((reflink $url desc id) $word+_2 ...) $top+_2 ...))
   (pre ($top+_1 ... ($word+_1 ... (reflink desc id_1)))
        (($word+_2 ...) $top+_2 ... ((linkref id_1 $url))))
   (where id_1 ,(if (seen-id? (term id))
                    (frsh)
                    (begin
                      (add-to-ids! (term id))
                      (term id))))]
  ;; reflink : title
  [(pre ($top+_1 ... ($word+_1 ...)) 
        (((reflink $url desc id titl) $word+_2 ...) $top+_2 ...))
   (pre ($top+_1 ... ($word+_1 ... (reflink desc id_1)))
        (($word+_2 ...) $top+_2 ... ((linkref id_1 $url titl))))
   (where id_1 ,(if (seen-id? (term id))
                    (frsh)
                    (begin
                      (add-to-ids! (term id))
                      (term id))))]
  ;; refimg : no title
  [(pre ($top+_1 ... ($word+_1 ...)) 
        (((refimg $url desc id) $word+_2 ...) $top+_2 ...))
   (pre ($top+_1 ... ($word+_1 ... (refimg desc id_1)))
        (($word+_2 ...) $top+_2 ... ((imgref id_1 $url))))
   (where id_1 ,(if (seen-id? (term id))
                    (frsh)
                    (begin
                      (add-to-ids! (term id))
                      (term id))))]
  ;; refimg : title
  [(pre ($top+_1 ... ($word+_1 ...)) 
        (((refimg $url desc id titl) $word+_2 ...) $top+_2 ...))
   (pre ($top+_1 ... ($word+_1 ... (refimg desc id_1)))
        (($word+_2 ...) $top+_2 ... ((imgref id_1 $url titl))))
   (where id_1 ,(if (seen-id? (term id))
                    (frsh)
                    (begin
                      (add-to-ids! (term id))
                      (term id))))]
  ;; refimg : no title or desc
  [(pre ($top+_1 ... ($word+_1 ...)) 
        (((refimg $url id) $word+_2 ...) $top+_2 ...))
   (pre ($top+_1 ... ($word+_1 ... (refimg id)))
        (($word+_2 ...) $top+_2 ... ((imgref id $url))))
   (side-condition (add-to-ids! (term id)))]
  ;; move to next $top
  [(pre ($top+_1 ...) (() $top+_2 ...)) (pre ($top+_1 ... ()) ($top+_2 ...))]
  ;; move to next $word
  [(pre ($top+_1 ... ($word+_1 ...)) (($word+ $word+_2 ...) $top+_2 ...))
   (pre ($top+_1 ... ($word+_1 ... $word+)) (($word+_2 ...) $top+_2 ...))])
  (term (pre (()) ,m)))

  
;; md->str --------------------------------------------------------------------
(define-metafunction MD
  md->str : any -> string
  [(md->str $md+) ,(mds->str (term $md+) "\n\n" #:after-last "\n\n")]
  [(md->str $words+) ,(mds->str (term $words+))]
  #;[(md->str (heading n $words))
   ,(let* ([words-str (mds->str (term $words))]
           [words-len (string-length words-str)])
      (case (random 3)
        [(0) (string-join (list (make-string (term n) #\#) words-str))]
        [(1) (string-join (list (make-string (term n) #\#) 
                                words-str
                                (make-string (term n) #\#)))]
        ;; underline only works for h1 or h2; ow default to atx-style
        [(2) (case (term n)
               [(1) (string-join 
                     (list words-str (make-string (add1 (random (* 2 (add1 words-len)))) #\=))
                     "\n")]
               [(2) (string-join
                     (list words-str (make-string (add1 (random (* 2 (add1 words-len)))) #\-))
                     "\n")]
               [else (string-join (list (make-string (term n) #\#) words-str))])]))]
;  [(md->str (quote $paras)) ,(mds->str (term $paras) "\n> ")]
;  [(md->str (olst $paras ...)) ,(mds->str (term ($paras ...)) "\n" #:numbered? #t)]
;  [(md->str (ulst $paras ...)) ,(mds->str (term ($paras ...)) "\n* ")]
  [(md->str (em str))
   ,(case (random 2)
      [(0) (wrap "*" (term str))]
      [(1) (wrap "_" (term str))])]
  [(md->str (strong str))
   ,(case (random 2)
      [(0) (wrap "**" (term str))]
      [(1) (wrap "__" (term str))])]
;  [(md->str (struck str)) ,(wrap "~~" (term str))]
  [(md->str (code str)) ,(wrap "`" (term str))]
;  [(md->str (anchor str)) str]
  ;; inline links
  [(md->str (inlink $url desc)) 
   ,(string-append "[" (term desc) "](" (term (url->str $url)) ")")]
  [(md->str (inlink $url desc titl)) 
   ,(string-append "[" (term desc) "](" (term (url->str $url)) " \"" (term titl) "\")")]
;  [(md->str (linkref url desc id titl))
;   ,(string-append "[" (term desc) "][" (term id) "]\n\n["
;                   (term id) "]: " (term url) "   \"" (term titl) "\"")] 
;  [(md->str (linkref url desc id titl))
;   ,(string-append "[" (term desc) "][" (term id) "]\n\n["
;                   (term id) "]: " (term url) "   \"" (term titl) "\"")] 
  ;; inline imgs
  [(md->str (inimg $url desc)) 
   ,(string-append "![" (term desc) "](" (term (url->str $url)) ")")]
  [(md->str (inimg $url desc titl)) 
   ,(string-append "![" (term desc) "](" (term (url->str $url)) " \"" (term titl) "\")")]
  ;; reference links
  [(md->str (reflink desc id)) 
   ,(string-append "[" (term desc) "][" (term id) "]")]
  [(md->str (linkref id $url)) 
   ,(string-append "[" (term id) "]: " (term (url->str $url)))]
  [(md->str (linkref id $url titl)) 
   ,(string-append "[" (term id) "]: " (term (url->str $url)) "  \"" (term titl) "\"")]
  ;; reference imgs
  [(md->str (refimg desc id)) 
   ,(string-append "![" (term desc) "][" (term id) "]")]
  [(md->str (refimg id)) 
   ,(string-append "![" (term id) "][]")]  
  [(md->str (imgref id $url))
   ,(string-append "[" (term id) "]: " (term (url->str $url)))]
  [(md->str (imgref id $url titl))
   ,(string-append "[" (term id) "]: " (term (url->str $url)) "  \"" (term titl) "\"")]
  [(md->str any) any])

(define (mds->str paras [sep " "] #:after-last [al ""] #:numbered? [numbered? #f])
  (define para-strs (map (λ (t) (term (md->str ,t))) paras))
  (define ps
    (if numbered?
        (for/list ([(p i) (in-indexed para-strs)]) 
          (string-append (number->string i) ". " p))
        para-strs))
  (string-join ps sep #:after-last al))

(define (wrap marks str) (string-append marks str marks))


(define-metafunction MD
  md->parsed : any -> any
  [(md->parsed $md+) ,(mds->parsed (term $md+))]
  [(md->parsed $words+) ,(words->parsed (term $words+))]
  [(md->parsed (inlink $url desc)) (a ((href (url->str $url))) desc)]
  [(md->parsed (inlink $url desc titl)) (a ((href (url->str $url)) (title titl)) desc)]
  [(md->parsed (reflink $url desc id)) 
   (a ((href (url->str $url))) desc)]
  [(md->parsed (reflink $url desc id titl)) 
   (a ((href (url->str $url)) (title titl)) desc)]
  [(md->parsed (inimg $url desc)) 
   (img ((src (url->str $url)) (alt desc)))]
  [(md->parsed (inimg $url desc titl)) 
   (img ((src (url->str $url)) (alt desc) (title titl)))]
  [(md->parsed (refimg $url desc id titl)) 
   (img ((src (url->str $url)) (alt desc) (title titl)))]
  [(md->parsed (refimg $url desc id)) 
   (img ((src (url->str $url)) (alt desc)))]
  [(md->parsed (refimg $url id)) 
   (img ((src (url->str $url)) (alt id)))]
  [(md->parsed (any str)) (any () str)]
  [(md->parsed any) any])

(define (mds->parsed paras) 
  (map 
   (match-lambda
     ;; special case img refs as the only element in a block
     [(and `(,img) `((refimg ,url ,desc ,id ,titl)))
      `(div ((class "figure"))
         ,(term (md->parsed ,img))
         (p ((class "caption")) ,desc))]
     [(and `(,img) `((refimg ,url ,desc ,id)))
      `(div ((class "figure"))
         ,(term (md->parsed ,img))
         (p ((class "caption")) ,desc))]
     [(and `(,img) `((refimg ,url ,id)))
      `(div ((class "figure"))
         ,(term (md->parsed ,img))
         (p ((class "caption")) ,id))]
     [(and `(,img) `((inimg ,url ,desc ,titl)))
      `(div ((class "figure"))
         ,(term (md->parsed ,img))
         (p ((class "caption")) ,desc))]
     [(and `(,img) `((inimg ,url ,desc)))
      `(div ((class "figure"))
         ,(term (md->parsed ,img))
         (p ((class "caption")) ,desc))]
     [t (term (p () ,@(combine-strs (term (md->parsed ,t)))))])
   paras))

(define (words->parsed words) 
  (add-between (map (λ (t) (term (md->parsed ,t))) words) " "))

  
;; consolidate consecutive string values
(define (combine-strs lst)
  (cond 
    [(null? lst) null]
   ; [(null? (cdr lst)) (list '(br ()))] ; convert last element to br
    [else
     (define-values (non-strs rst1) (splitf-at lst (compose not string?)))
     (define-values (strs rst2) (splitf-at rst1 string?))
     (append non-strs (if (null? strs) null (list (apply string-append strs))) (combine-strs rst2))]))
     
(require "../parse.rkt")
(define n 0)
(define (checker m [debug #f])
  (define filtered (filter-not null? m)) ; drop empty samples
  (define preprocessed (pre filtered))
  (define mdstr (term (md->str ,preprocessed)))
  (define parsed (parse-markdown mdstr))
  (define expected (term (md->parsed ,filtered)))
  ;; debugging printfs
  (when (zero? (modulo n 100)) (printf "~a " n)) (set! n (add1 n))
  (when debug
    (printf "generated: ---------------------------------------------------\n")
    (pretty-print m)
    (printf "filtered: ----------------------------------------------------\n")
    (pretty-print filtered)
    (printf "preprocessed: ------------------------------------------------\n")
    (pretty-print preprocessed)
    (printf "as string: ---------------------------------------------------\n")
    (printf "~s\n" mdstr)
    (printf "parsed: ------------------------------------------------------\n")
    (pretty-print parsed)
    (printf "expected: ----------------------------------------------------\n")
    (pretty-print expected))
  ;; print more debugging info on fail
  (if debug 
      (equal? parsed expected)
      (or (equal? parsed expected) (checker m #t))))
        

(redex-check MD $md (checker (term $md))
             #:attempts 1000 #:attempt-size (λ _ 4))