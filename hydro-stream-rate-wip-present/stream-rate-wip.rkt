#lang slideshow

(require racket/runtime-path
         slideshow/latex
         slideshow/extras
         slideshow/step
         pict/shadow)

;; Cache pngs in a subdirectory; without this, it's the user's temp dir
(setup-local-latex-cache)

;; We want to see the whole log when there are errors (the log parser doesn't
;; always find them, because LaTeX doesn't have a standard error format), and
;; we want little info messages about whether pngs are built or just loaded
(latex-debug? #t)

;; Added to every tex file, before the document proper:
(add-preamble
 #<<latex
\usepackage{amsmath, amssymb}
\newcommand{\targetlang}{\lambda_{\mathrm{ZFC}}}
\newcommand{\meaningof}[1]{[\![{#1}]\!]}  % use in semantic functions
\newcommand{\A}{\mathcal{A}}
\renewcommand{\P}{\mathbb{P}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\R}{\mathbb{R}}
latex
 )

;; =============================================================================
;; Some general helper functions and initialization definitions

(current-main-font "C059")
(current-title-color "Navy")
(set-margin! 60)

(define bgcolor "Lavender Blush")
(define accent1 "Navy")
(define accent2 "Saddle Brown")
(define accent3 "Orchid")
(define hlcolor "Light Pink")

(define lambda-st ($"\\lambda^{ST}"))

(set-page-numbers-visible! #f)

;; Background parameters
(define background-image (make-parameter #f))
(define (background-image-pict)
   (define bg (background-image))
   (inset (scale bg (/ 1024 (pict-width bg)) (/ 768 (pict-height bg)))
          (- margin)))

;; Slide number parameters
(define slide-number (make-parameter 0))
(define (add1-slide-number) (slide-number (add1 (slide-number))))
(define format-slide-number
   (make-parameter
    (lambda (num)
      (scale (rt (number->string (slide-number))) 3/5))))

;; Slide assembly
(define (add-slide bg-pct pct)
   (refocus (cc-superimpose bg-pct pct) bg-pct))

(define (add-slide-number pct)
   (refocus
    (rb-superimpose pct ((format-slide-number) (slide-number)))
    pct))

(current-slide-assembler
  (let ([orig  (current-slide-assembler)])
    (lambda (title sep body)
      (let* ([pct  (if (background-image)
                       (background-image-pict)
                       (inset (blank 1024 768) (- margin)))]
             [pct  (add-slide pct (orig title sep body))]
             [pct  (if (slide-number) (add-slide-number pct) pct)])
        pct))))

(define base-bg (filled-rectangle client-w client-h #:color bgcolor))
(define hl-bg (filled-rectangle client-w client-h #:color "Cornsilk"))

;; Highlight
(define (hl pct add-size)
  (cc-superimpose (colorize
                   (filled-rounded-rectangle (+ (pict-width pct) add-size) (+ (pict-height pct) add-size))
                   hlcolor)
                  pct))

;; =============================================================================
;; Title slide
(slide-number 1)
(background-image
 (pin-over base-bg
           0 80
           (pin-over
            (pin-over
             (colorize (filled-rectangle client-w 20) accent3)
             (- client-w 100) -10
             (colorize (disk 45) accent2))
            300 -10
            (colorize (disk 45) accent2))))
(slide
 (vl-append 40
  (vl-append
    (colorize (text "Rate Limit" (current-main-font) 100) accent1)
    (colorize (text "Refinement Types" (current-main-font) 100) accent1))
  (vr-append 10
    (vl-append 10
      (text "work-in-progress" (current-main-font) 28)
      (it "Lucas Du and Caleb Stanford"))
    (text "UC Davis" (current-main-font) 28))))

(add1-slide-number)
(background-image base-bg)
(slide
 (vl-append
  10
  (colorize (text "Large-scale" (cons 'bold (current-main-font)) 54) accent1)
  (colorize (text "stream-processing programs" (cons 'bold (current-main-font)) 48) accent1)
  (para "are widely used in industry for high-volume, real-time data ingestion and analysis.")))

(add1-slide-number)
(slide
 (vl-append
  10
  (colorize (text "Lots of pitfalls..." (cons 'bold (current-main-font)) 54) accent1)
  (item "Ordering, causality")
  (item "Distribution, parallelism")
  (item "Latency, throughput, load-management")))

(add1-slide-number)
(slide
 (vc-append
  10
  (colorize (text "A lack of" (cons 'italic (current-main-font)) 48) accent3)
  (colorize (text "programming language" (cons 'bold (current-main-font)) 60) accent2)
  (colorize (text "and correctness" (cons 'bold (current-main-font)) 60) accent2)
  (colorize (text "support" (cons 'italic (current-main-font)) 48) accent3)))

(define dataflow-graph-nodes
  (let ([node1 (colorize (disk 45) accent2)]
        [node2 (colorize (disk 45) accent2)]
        [node3 (colorize (disk 45) accent2)]
        [node4 (colorize (disk 45) accent2)]
        [node5 (colorize (disk 45) accent2)]
        [node6 (colorize (disk 45) accent2)])
    (define df-nodes (hc-append 200 node1 (vc-append 100 node2 node3 node4) (vc-append 100 node5 node6)))
    ;; There must be a more concise way to do this lmfao
    (pin-arrow-line
     10 (pin-arrow-line
        10 (pin-arrow-line
            10 (pin-arrow-line
                10 (pin-arrow-line
                    10 (pin-arrow-line
                        10 (pin-arrow-line
                            10 (pin-arrow-line
                                10 (pin-arrow-line
                                    10 df-nodes node1 rc-find node2 lc-find
                                    #:line-width 3 #:color accent3
                                    #:label (hl (colorize (text "S | φ" (current-main-font) 15) accent1) 5))
                                node1 rc-find node3 lc-find #:line-width 3 #:color accent3
                                #:label (hl (colorize (text "S | φ" (current-main-font) 15) accent1) 5))
                            node1 rc-find node4 lc-find #:line-width 3 #:color accent3
                            #:label (hl (colorize (text "S | φ" (current-main-font) 15) accent1) 5))
                        node3 rc-find node5 lc-find #:line-width 3 #:color accent3)
                    node3 rc-find node6 lc-find #:line-width 3 #:color accent3)
                node4 rc-find node5 lc-find #:line-width 3 #:color accent3
                #:label (hl (colorize (text "S | φ" (current-main-font) 15) accent1) 5))
            node4 rc-find node6 lc-find #:line-width 3 #:color accent3
            #:label (hl (colorize (text "S | φ" (current-main-font) 15) accent1) 5))
        node2 rc-find node5 lc-find #:line-width 3 #:color accent3
        #:label (hl (colorize (text "S | φ" (current-main-font) 15) accent1) 5))
     node2 rc-find node6 lc-find #:line-width 3 #:color accent3
     #:label (hl (colorize (text "S | φ" (current-main-font) 15) accent1) 5))))

(add1-slide-number)
(slide
 (colorize (text "A vision for verified dataflow" (cons 'bold (current-main-font)) 40) accent1)
 (cc-superimpose
  titleless-page
  (vc-append 30
   dataflow-graph-nodes
   (ht-append
    20
    (hl (colorize (text "S | φ" (cons 'bold (current-main-font)) 40) accent1) 10)
    (para "Where S a stream and φ is some property. In other words, a" (it "refinement type") "or" (it "(property type)") ".")))))

(add1-slide-number)
(slide
 (vr-append
  20
  (vl-append
   10
   (colorize (text "Our special interest..." (cons 'italic (current-main-font)) 32) accent2)
   (colorize (text "Language support for reasoning about" (current-main-font) 40) accent2))
  (colorize (text "rates & load" (cons 'bold (current-main-font)) 80) accent1)
  (vr-append
   10
   (colorize (text "What could go wrong?" (cons 'italic (current-main-font)) 32) accent2)
   (colorize (text "Latency spikes" (current-main-font) 28) accent2)
   (colorize (text "Dropped events" (current-main-font) 28) accent2)
   (colorize (text "Service outages" (current-main-font) 28) accent2)
   (colorize (text "etc." (current-main-font) 28) accent2))))

(add1-slide-number)
(slide
 (vl-append
  20
  (colorize (text "What do we want?" (cons' bold (current-main-font)) 48) accent2)
  (item "A" (bt "refinement type system for stream rates") ", based on the \"Stream Types\"" ($"\\lambda^{ST}") "calculus (Cutler et. al., PLDI 2024).")
  (item "A" (bt "semantics") "based on" (it "timed languages."))
  (item "An efficient type checking algorithm.")
  (item "An implementation and corresponding evaluation of the type system.")))

(add1-slide-number)
(background-image
 (pin-over base-bg
           0 80
           (pin-over
            (pin-over
             (colorize (filled-rectangle client-w 20) accent3)
             (- client-w 80) -10
             (colorize (disk 45) accent2))
            (- client-w 400) -10
            (colorize (disk 45) accent2))))
(slide
 (para "In particular, we want to use" (bt "types") "to reason about the" (it "rate behavior of a stream program") "in a" (bt "principled") "and" (bt "compositional") "way.")
 'next
 (item "Can a stream with some rate safely be used in place of another?")
 (item "Can two stream programs fit together without buffering at the boundary? Can we put a bound on any buffering needed?")
 (item "How does a stream operator transform an input rate into an output rate?"))

;; connection to Hydro here:
;; we want to implement on top of an existing, well-engineered system that cares about some of these same issues
;; would be interesting to use for DSL implementation and evaluation

(add1-slide-number)
(background-image base-bg)
(slide
 (hc-append 10
            (t "For now, we focus on")
            (colorize (text "subtyping" (cons 'bold (current-main-font)) 50) accent1))
 'next
 (hl (item "Can a stream with some rate safely be used in place of another?") 30))

(add1-slide-number)
(background-image base-bg)
(slide
 (text "A grammar for stream rates" (current-main-font) 40)
 (scale (colorize ($"S \\mathrel{::=} @n/t\\ |\\ S+S\\ |\\ S \\cdot S\\ |\\ S \\parallel S\\ |\\ S\\land S") accent2) 1.2))

(add1-slide-number)
(slide
 (scale (colorize ($"S \\mathrel{::=} @n/t\\ |\\ S+S\\ |\\ S \\cdot S\\ |\\ S \\parallel S\\ |\\ S\\land S") accent2) 1.3)
 (para "Note that this kind of model, taken from" lambda-st ", gives us a" (it "richer structure") "than standard models of streams.")
 (para "We can precisely describe streams with " (it "concatenation") "," (it "sum/tagged union") ", and" (it "parallelism") ".")
 (para "We can also give multiple rate types to a stream with" ($"\\land") "."))

(add1-slide-number)
(slide
 (vl-append
  30
  (colorize (text "Two kinds of rate distributions" (cons 'italic (current-main-font)) 24) "black")
  (colorize (text "1. uniform (or sliding) rates" (cons 'bold (current-main-font)) 40) accent1)
  (colorize (text "2. segmented (or tumbling) rates" (cons 'bold (current-main-font)) 40) accent1))
 'next
 (para "This is a relatively standard classification.")
 (hl (para "More interestingly, it maps well onto the kinds of distributions enforced by practical rate-limiting algorithms.") 70))

;; explain both kinds of distributions, stick with sliding
;; try to use a diagram
(add1-slide-number)
(slide
 titleless-page)

;; explain raw/base subtyping in the sliding setting
(add1-slide-number)
(slide
 ($"@n_1/t_1 \\mathrel{<:} @n_2/t_2"))
;; try to use a diagram

;; explain problems when we add in our richer type constructors
;; i.e. there's no compositional way to combine S₁ + S₂  if there's no immediate subtyping relation
;; same for S₁ || S₂, for example (the problem is even worse here, actually)
;; what do we do? well, there's some connection here to (concurrent) Kleene algebras and regular languages
;; put the Kleene algebra rules up
;; maybe we can simplify things using some kind of Kleene algebra?
;; so let's try to formalize some connections!
;; automata --- tick and timed automata
;; seems pretty expensive to directly do inclusion on these though...
;; so maybe, let's prove a Kleene theorem that allows us to do Kleene algebra rewrites based on the automata semantics
;; and then use that algebra to simplify our typechecking
;; and use some sound (but possibly incomplete) abstractions to actually decide subtyping more efficiently!
;; a sketch of the ideas:
;; - Kleene-like algebra rules for rewriting and simplifying full rate types
;; - a core boolean algebra of rates that all full rate types can be lowered to
;; - some sound abstractions to get our boolean algebra to a normal form that is easily subtypable
;; - check subtyping by deciding implication/entailment
