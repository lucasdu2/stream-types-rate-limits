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
  (colorize (text "Lots of pitfalls:" (cons 'bold (current-main-font)) 60) accent2)
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

(add1-slide-number)
(slide
 (colorize (text "A vision for verified dataflow" (cons 'bold (current-main-font)) 48) accent1)
 (colorize (t "(todo: add dataflow diagram, refinement type drawing)") "crimson"))

(add1-slide-number)
(slide
 (vr-append
  20
  (vl-append
   10
   (colorize (text "Our special interest..." (cons 'italic (current-main-font)) 32) accent3)
   (colorize (text "Language support for reasoning about" (current-main-font) 40) accent3))
  (colorize (text "rates & load" (cons 'bold (current-main-font)) 80) accent1)
  (vr-append
   10
   (colorize (text "What could go wrong?" (cons 'italic (current-main-font)) 32) accent3)
   (colorize (text "Latency spikes" (current-main-font) 28) accent3)
   (colorize (text "Dropped events" (current-main-font) 28) accent3)
   (colorize (text "Service outages" (current-main-font) 28) accent3)
   (colorize (text "etc." (current-main-font) 28) accent3))))

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
 (item "Can a stream with some rate safely be used in place of another?")
 (item "Can two stream programs fit together without rate-limiting or buffering at the boundary?")
 (item "How does a stream operator transform an input rate into an output rate?"))

(add1-slide-number)
(background-image base-bg)
(slide
 (scale (colorize ($"S \\mathrel{::=} @n/t\\ |\\ S+S\\ | S \\cdot S\\ |\\ S \\parallel S\\ |\\ S\\land S") accent2) 1.2))
