#lang slideshow

;; NOTE: Golden rule: when introducing notation, must give a corresponding example
;; whole p∮of notation is to abstract examples

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
\usepackage{amsmath, amssymb, mathpartir}
\newcommand{\targetlang}{\lambda_{\mathrm{ZFC}}}
\newcommand{\meaningof}[1]{[\![{#1}]\!]}  % use in semantic functions
\newcommand{\A}{\mathcal{A}}
\renewcommand{\P}{\mathbb{P}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\Z}{\mathbb{Z}}
\newcommand{\Q}{\mathbb{Q}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\ceil}[1]{\lceil {#1} \rceil}
\newcommand{\floor}[1]{\lfloor {#1} \rfloor}
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
(define hl-bg (filled-rectangle client-w client-h #:color "Sea Shell"))

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
;; Rate Limit Types for Stream Programs
(slide
 (vl-append
  40
  (blank)
  (blank)
  (vl-append
    (colorize (text "Rate Limit Types" (current-main-font) 90) accent1)
    (colorize (text "for Stream Programs" (current-main-font) 70) accent1))
  (hc-append 80
  (vr-append 10
    (vl-append 10
      (text "work-in-progress" (current-main-font) 28)
      (it "Lucas Du and Caleb Stanford"))
    (text "UC Davis" (current-main-font) 28))
 (scale (bitmap "water-tower-ucd.png") 0.06))))

(add1-slide-number)
(background-image base-bg)
(slide
 (vl-append
  15
  (colorize (text "Large-scale" (cons 'bold (current-main-font)) 54) accent1)
  (colorize (text "stream-processing programs" (cons 'bold (current-main-font)) 48) accent1)
  (para "are widely used in industry for high-volume, real-time data ingestion and analysis.")
  (hc-append 50 (scale (bitmap "flink-squirrel.png") 0.8) (scale (bitmap "kafka.png") 0.05) (scale (bitmap "hydro.png") 0.6))))

(add1-slide-number)
(slide
  (colorize (text "Some programming challenges" (cons 'bold (current-main-font)) 48) accent1)
  (text "...ordering guarantees, causality, automatic distribution, efficient parallellism, low latency, high throughput..." (current-main-font) 18)
  (hl (text "load-management" (cons 'bold (current-main-font)) 40) 40))

(add1-slide-number)
(slide
 (item (it "Manage load") (bt "by limiting rate"))
 (item "e.g. at most 5 events every 10 seconds, or at most 10000 requests every hour")
 'next
 (item "Commonly used by public-facing APIs, i.e. Github's API, Shopify's API, or LLM APIs")
 (subitem "Github's API currently allows authenticated users 5000 requests per hour")
)

 ;; 'next
 ;; (item "Generally, an enforceable contract between two programs that communicate through real-time data streams")
 ;; (item "An upper bound on the rate of a stream")

(add1-slide-number)
(slide
 (vc-append
  10
  (colorize (text "Can we get more" (cons 'italic (current-main-font)) 48) accent3)
  (colorize (text "programming language" (cons 'bold (current-main-font)) 60) accent2)
  (colorize (text "and correctness" (cons 'bold (current-main-font)) 60) accent2)
  (colorize (text "support?" (cons 'italic (current-main-font)) 48) accent3)))

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
(background-image hl-bg)
(slide
 (colorize (text "A vision for verified stream programming" (cons 'bold (current-main-font)) 40) accent1)
 (cc-superimpose
  titleless-page
  (vc-append 30
   dataflow-graph-nodes
   (ht-append
    20
    (hl (colorize (text "S | φ" (cons 'bold (current-main-font)) 40) accent1) 10)
    (para "Where S a stream and φ is some property. In other words, a" (it "refinement type") "or" (it "(property type)") "."))
   (para "(For us, the φs we care about are" (bt "stream rates") ".)"))))

(add1-slide-number)
(background-image base-bg)
(slide
 (vl-append
  20
  (colorize (text "Contributions (WIP)" (cons' bold (current-main-font)) 48) accent2)
  (item "A" (bt "refinement type system for stream rates."))
  (item "A" (bt "semantics") "based on" (it "timed regular languages."))
  (item "An efficient type checking algorithm.")
  (item "An implementation and corresponding evaluation of the type system.")))

(background-image base-bg)
(slide
 (vl-append
  20
  (colorize (text "Contributions (WIP)" (cons' bold (current-main-font)) 48) accent2)
  (item "A" (bt "refinement type system for stream rates."))
  (colorize (item "A" (bt "semantics") "based on" (it "timed regular languages.")) "gray")
  (colorize (item "An efficient type checking algorithm.") "gray")
  (colorize (item "An implementation and corresponding evaluation of the type system.") "gray")))

(add1-slide-number)
(background-image hl-bg)
(slide
 (colorize (text "A brief aside" (cons 'bold (current-main-font)) 40) accent1)
 (para "For implementation and evaluation, we would like to use some existing, well-engineered systems infrastructure for distributed stream processing.")
 (para "Hydro seems like a great choice!")
 (para "(And we would love to collaborate!)")
 (scale (bitmap "hydro.png") 0.5))

(add1-slide-number)
(background-image base-bg)
(slide
 (colorize (text "What is a stream rate?" (cons 'bold (current-main-font)) 50) accent1)
 'alts
 (list
  (list (item "for our purposes, 2 parts: an event count (n) and a window size (t)")
        (item "(at most) n events per each window of size t")
        'next
        (item "a sound static abstraction to reason about dynamic behavior of stream rates in the wild"))
  (list (vc-append 20
                   (scale (bitmap "github-rate-limit.png") 0.6)
                   (scale (bitmap "shopify-rate-limit.png") 0.6)
                   (scale (bitmap "claude-rate-limit.png") 0.6)))
  (list
   (item (bt "latency spikes:") "as requests get backed up and added to a buffer, requests start taking longer to return")
   (item (bt "dropped events:") "some events/requests may just be dropped and not processed")
   (item (bt "service outage:") "maybe machines crash because they are overloaded"))
  (list
   (para "When we compose program A with program B, and A's output rate exceeds B's input rate limit, we may run into these kinds of problems."))
  (list
   (para "What is a type structure that can model stream rates?"))))

(add1-slide-number)
(background-image base-bg)
(slide
 #:layout 'top
 (scale (colorize ($"@n/t") accent2) 1)
 (hline 500 10)
 'next
 (item "n events in every window of size t units")
 (item ($"@10/5") "means 10 events in every 5 unit window"))
;; \\ |\\ S+S\\ |\\ S \\cdot S\\ |\\ S \\parallel S\\ |\\ S^*\\ |\\ S\\land S")

(add1-slide-number)
(background-image base-bg)
(slide
 #:layout 'top
 (scale (colorize ($"S_1 \\cdot S_2") accent2) 1)
 (hline 500 10)
 'next
 (item ($"S_1") "and" ($"S_2") "are stream rate types (so our definition is recursive)")
 (item "a stream of rate" ($"S_1") (bt "followed by") "a stream of rate" ($"S_2"))
 (item ($"@10/5 \\cdot @12/6")))

(add1-slide-number)
(background-image base-bg)
(slide
 #:layout 'top
 (scale (colorize ($"S_1 + S_2") accent2) 1)
 (hline 500 10)
 'next
 (item "a stream of rate" ($"S_1") (bt "or") "rate" ($"S_2"))
 (item ($"@10/5 + @12/6")))

(add1-slide-number)
(background-image base-bg)
(slide
 #:layout 'top
 (scale (colorize ($"S_1 \\parallel S_2") accent2) 1)
 (hline 500 10)
 'next
 (item "a stream of rate" ($"S_1") (bt "in parallel with") "a stream of rate" ($"S_2"))
 (item ($"@10/5 \\parallel @12/6")))

(add1-slide-number)
(background-image base-bg)
(slide
 #:layout 'top
 (scale (colorize ($"S_1 \\land S_2") accent2) 1)
 (hline 500 10)
 'next
 (item "a stream of rate" ($"S_1") (bt "and") "rate" ($"S_2"))
 (item ($"@10/5 \\land @12/6")))

(add1-slide-number)
(slide
 (vl-append
  20
  (colorize (text "Stream rate semantics" (cons 'bold (current-main-font)) 30) "black")
  (colorize (text "Two main kinds of rate distributions" (cons 'italic (current-main-font)) 24) "black")
  (colorize (text "1. segmented (or tumbling) rates" (cons 'bold (current-main-font)) 40) accent1)
  (colorize (text "2. uniform (or sliding) rates" (cons 'bold (current-main-font)) 40) accent1))
 (para "(For example, Github enforces a tumbling rate and Shopify enforces a sliding rate. Claude enforces a sliding rate.)"))

;; NOTE: Tumbling rates allow bursts at window boundaries. Is a subtype of the
;; corresponding uniform rate with double the number of events, same window size.
;; Often comes with multiple rate limits in practice, one primary one that is
;; more coarse-grained, and one secondary one that is more fine-grained, i.e.
;; 5,000 events/1 hour and 100 events/1s, the latter of which is used to control
;; burstiness.
(add1-slide-number)
(slide
 (colorize (text "Tumbling rates" (cons 'bold (current-main-font)) 50) accent1)
 (para "Github: tumbling rate of 5000 requests per 1 hour, with fixed 1 hour windows starting from time of first request")
 (blank)
 (blank)
 (blank)
 (blank)
 (blank))

(add1-slide-number)
(slide
 (colorize (text "Sliding rates" (cons 'bold (current-main-font)) 50) accent1)
 (para "Shopify: sliding rate of 1000 \"points\" per 60 seconds, for any arbitrary 60 second window")
 (blank)
 (blank)
 (blank)
 (blank)
 (blank))

(add1-slide-number)
(slide
 (para "From now on, we will focus solely on" (bt "sliding rates") ", for the sake of simplicity. Other interesting things happen when we consider tumbling rates and combinations of sliding and tumbling rates! But we won't talk about those things here."))


(add1-slide-number)
(slide
 (para "Reasoning about rate limits is still largely a manual process.")
 (para "This can get complicated and unwieldy when stream programs get larger and more complex."))

(add1-slide-number)
(slide
 (para "Even relatively simple cases can be tricky to reason about.")
 'next
 (para "For example, Shopify allows a sliding rate of 1000 points per 60 seconds.")
 'next
 (para "Say we have a program that sends a stream of requests to our Shopify API endpoint at a rate of 2000 points per 120 seconds. Are we guaranteed to remain under the rate limit?"))

(add1-slide-number)
(slide
 (vc-append
  10
  (colorize (text "Can we get more" (cons 'italic (current-main-font)) 48) accent3)
  (colorize (text "programming language" (cons 'bold (current-main-font)) 60) accent2)
  (colorize (text "and correctness" (cons 'bold (current-main-font)) 60) accent2)
  (colorize (text "support?" (cons 'italic (current-main-font)) 48) accent3)))

(add1-slide-number)
(slide
 (para "Can we design a" (bt "refinement type system") "to help us reason about rate limits?")
 (para "Types offer a lightweight, interactive way to automate lots of tricky reasoning!")
 'next
 (para "More concretely: Can problems like" (it "safe rate composability") "(i.e. the previous Shopify API example) be reduced to a" (bt "property of type safety") "?"))

(add1-slide-number)
(background-image base-bg)
(slide
 (vc-append 10
            (t "A key piece any refinement type system is the question of")
            (colorize (text "subtyping" (cons 'bold (current-main-font)) 50) accent1))
 'next
 (para "Practically speaking, can one stream fit safely into another?")
 'next
 (para "More concretely, remember our Shopify example: Does a stream with sliding rate of 2000 points per 120 seconds fit safely into a stream with sliding rate of 1000 points per 60 seconds?")
 'next
 (hl (para "From a general type system perspective, subtyping allows flexibility: i.e. can we safely cast an int to a float (or, similarly, use an int in place of a float)?") 50))




;; TODO: More examples, less math
;; TODO: More motivation, what worked/what didn't
;; TODO: Subtyping rule slide --- can possibly keep, but give more examples on the previous slide
;; TODO: can work up to the rate type subtyping for "raw" rates very slowly, then introduce one
;; problem, i.e. the problem with the parallel operator (not general or composable)
;; TODO: Picture of timeline, when I introduce rate types
;; TODO: Maybe still include tumbling for reference, but will need to explain (i.e. Github API)
;; Counterexample for why 10/5 is not a subtype of 12/6

;; Caleb feedback
;; way more examples (examples throughout)
;; Github API, Shopify API, how they do rate limiting
;; limited to 100 per day, shopify does a sliding window approach
;; example first, then definition

;; add checks and xs for correct and incorrect subtypes
(add1-slide-number)
(slide
 (colorize (text "Subtyping for \"raw\" rate types" (cons 'bold (current-main-font)) 40) accent1)
 (para "we will use the" ($"\\mathrel{<:}") "symbol to represent a subtyping relationship")
 ($"@n_1/t_1 \\mathrel{<:} @n_2/t_2")
 (hline 500 10)
 'next
 'alts
 (list
  (list ($"@10/5 \\mathrel{<:?} @12/5"))
  (list (hc-append 10 ($"@10/5 \\mathrel{<:?} @12/5") (scale (bitmap "green-check.png") 0.5))))
 'next
 'alts
 (list
  (list ($"@10/5 \\mathrel{<:?} @12/6"))
  (list (hc-append 10 ($"@10/5 \\mathrel{<:?} @12/6") (scale (bitmap "red-x.png") 0.5))))
 'next
 'alts
 (list
  (list ($"@10/5 \\mathrel{<:?} @22/6"))
  (list (hc-append 10 ($"@10/5 \\mathrel{<:?} @22/6") (scale (bitmap "green-check.png") 0.5))))
 'next
 'alts
 (list
  (list ($"@40/6 \\mathrel{<:?} @40/5"))
  (list (hc-append 10 ($"@40/6 \\mathrel{<:?} @40/5") (scale (bitmap "green-check.png") 0.5))))
 'next
 'alts
 (list
  (list ($"@41/6 \\mathrel{<:?} @40/5"))
  (list (hc-append 10 ($"@41/6 \\mathrel{<:?} @40/5") (scale (bitmap "red-x.png") 0.5)))))

(add1-slide-number)
(slide
 ($"\\inferrule [raw-rate-sub]{(t_2 < t_1 \\land n_1 \\leq n_2) \\lor (t_1 \\leq t_2 \\land n_1 \\leq n_2/(\\ceil{t_2/t_1}))}{@n_1/t_1 \\leq @n_2/t_2}"))

(add1-slide-number)
(slide
 (colorize (text "What happens with more complex types?" (cons 'italic (current-main-font)) 40) accent1)
 (t "i.e. ones that use more of our grammar."))

(add1-slide-number)
(slide
 (para "For certain type structures, we have simple solutions. For example:")
 ($"\\inferrule [concat-both-sub]{S_1 \\mathrel{<:} S_3 \\land S_2 \\mathrel{<:} S_4}{(S_1 \\cdot S_2) \\mathrel{<:} (S_3 \\cdot S_4)}"))
(add1-slide-number)
(slide
 (para "But others, particularly ones that involve parallelism and concatenation, are problematic.")
 'next
 (colorize ($"@10/3 \\parallel @12/5 \\mathrel{<:?} @40/4 \\parallel @10/5") accent1)
 'next
 (colorize ($"@7/5 \\cdot @16/13 \\mathrel{<:?} @10/6") accent1))

(add1-slide-number)
(slide
 (para "Let's focus on the case with parallelism.")
 (colorize ($"@10/3 \\parallel @12/5 \\mathrel{<:?} @40/4 \\parallel @10/5") accent1)
 (para "What can we do?")
 'next
 (para "Maybe we can take apart each parallel rate and check the individual parts separately?")
 (colorize ($"@10/3 \\mathrel{<:?} @40/4") accent1)
 (colorize ($"@12/5 \\mathrel{<:?} @10/5") accent1)
 'next
 (para "Why might this not work?"))

(add1-slide-number)
(slide
 (para "We can attempt to solve this problem by")
 (it "abstracting sound upper and lower bounds")
 (para "for problematic constructors, and using those bounds in our subtype checks.")
 'next
 (hc-append 5 (hl ($"@a/b") 10) ($"\\mathrel{<:} @n_1/t_1 \\parallel @n_2/t_2"))
 (hc-append 5 ($"@n_1/t_1 \\cdot @n_2/t_2 \\mathrel{<:}")(hl ($"@a/b") 10)))

(add1-slide-number)
(slide
 (para "And indeed, there are some plausible ways we can do this. Again, let's focus on the parallelism case.")
 (colorize ($"@10/3 \\parallel @12/5 \\mathrel{<:?} @40/4 \\parallel @10/5") accent1)
 'next
 (hc-append 5 (hl ($"@a_1/b_1") 10) ($"\\mathrel{<:} @40/4 \\parallel @10/5"))
 'next
 (hc-append 5 (hl ($"@(40 + 10)/5") 10) ($"\\mathrel{<:} @40/4 \\parallel @10/5"))
 'next
 (hc-append 5 ($"@10/3 \\parallel @12/5 \\mathrel{<:}") (hl ($"@a_2/b_2") 10))
 'next
 (hc-append 5 ($"@10/3 \\parallel @12/5 \\mathrel{<:}") (hl ($"@(20 + 12)/5") 10))
 'next
 (hc-append 10 ($"@(20 + 12)/5 \\mathrel{<:} @(40 + 10)/5") (scale (bitmap "green-check.png") 0.5)))

(add1-slide-number)
(slide
 (para "But this abstraction is neither")
 (bt "general nor composable")
 'next
 (para "Not only does this abstraction not work over general stream types, but this abstraction just over the set of \"raw\" rates does not form a lattice, i.e. there is no notion of least upper bound/greatest lower bound for pairs of \"raw\" rates.")
 'next
 (para "For example, let's try to compare some upper bounds on:")
 ($"@10/3 \\parallel @12/5"))

(add1-slide-number)
(slide
 (para "When might this be a problem? Here's a slightly more complicated example:")
 (colorize (scale ($"@10/3 \\parallel @12/5 \\parallel @20/10 \\mathrel{<:} @500/1000 \\parallel @36/40 \\parallel @75/60") 0.8) accent1)
 'next
 (para "If there's no least upper bound and greatest lower bound for parallel pairs of \"raw\" rates, how do we choose what window size to use?"))

(add1-slide-number)
(slide
 (colorize (text "(Concurrent) Kleene algebra?" (cons 'bold (current-main-font)) 40) accent3)
 (item "The observation here is the Kleene algebra already looks very similar to our stream rate types.")
 'next
 (colorize (text "Regular languages?" (cons 'bold (current-main-font)) 40) accent3)
 'next
 (colorize (text "Finite state and/or timed automata?" (cons 'bold (current-main-font)) 40) accent3)
 'next
 (para "Maybe, but it seems like directly checking inclusion on some kind of rate automata is very expensive.")
 (para "possibly EXPTIME on window size?"))

(add1-slide-number)
(slide
 (colorize (text "Interesting directions" (cons 'bold (current-main-font)) 40) accent2)
 (item "Develop a model for rates with a regular (timed) automata.")
 (item "Prove a Kleene theorem that allows us to algebraically/equationally manipulate and simplify a regular language for rates.")
 (item "Introduce sound abstractions over the underlying automata model (some abstract interpretation) that further reduce the regular language to a boolean-like algebra of rates.")
 (item "Decide implication/entailment between two rates in the boolean-like algebra, aka subtyping."))

(add1-slide-number)
(slide
 (colorize (text "Summary" (cons 'bold (current-main-font)) 40) accent1)
 (item "Rate limits, why they matter, and how types might help.")
 (item "Some ideas for how to solve the subtyping problem for one formulation of a rate type system.")
 (item "Pointers towards directions that may help solve some outstanding issues.")
 (item "Hydro as a compilation target for implementation and evaluation! Possible opportunities for collaboration? :)"))
