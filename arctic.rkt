#lang racket
(require pict)
;; Arctic circle maths

;; Aztec pyramid tiling
;; Generate a random Aztec pyramid recursively by orienting and shifting tiles as in
;;
;; https://www.youtube.com/watch?v=Yy7Q8IWNfHM

;; An A(1) pyramid is 2x2 tiled by 2 dominoes as either || or =.
;; An A(2) pyramid is
;;  ..
;; ....
;; ....
;;  ..
;; An A(3) pyramid is
;;   ..
;;  ....
;; ......
;; ......
;;  ....
;;   ..
;; etc, adding left and right squares on each line and capping ../.. on top and bottom.
;;
;;
;; A Board[n] is a vector[vector[state, 2n], 2n] indexed by row, column.

;; For less allocation, we can embed Any A(n) in a single 2m square matrix where m >= n
;; and iterate the expansion without allocating new boards.

;; in-aztec? Nat Nat Nat -> Bool
;; Returns true iff the given cell is in the A(size) Aztec pyramid.
;; Examples:
;; (in-aztec? 1 0 0) => true
;; (in-aztec? 2 0 0) => false
;; (in-aztec? 2 1 0) => true
(define (in-aztec? size row col)
  (define dim (* 2 size))
  (cond
    ;; Simple boundary conditions.
    [(or (< row 0) (< col 0) (>= row dim) (>= col dim)) #f]
    ;; For both row < size and col < size, we have a rising staircase.
    ;; If a dimension is >= size, then reflect over the midpoint.
    [else
     ;; Collapse all the symmetries to just talk about the rising staircase.
     (define q1row (if (< row size) row (- dim (add1 row))))
     (define q1col (if (< col size) col (- dim (add1 col))))
     (>= q1col (- size (add1 q1row)))]))

(define (empty-board size)
  (define dim (* 2 size))
  (for/vector ([_ (in-range dim)])
    (make-vector dim 'AM)))

(define (board-size board)
  (/ (vector-length board) 2))

(define (board-set! board row col state)
  (vector-set! (vector-ref board row) col state))

(define (board-ref board row col)
  (vector-ref (vector-ref board row) col))

(define (empty-cell? state)
  (eq? state 'EM))

(define (domino-down? state)
  (eq? state 'DD))

(define (domino-up? state)
  (eq? state 'DU))

(define (domino-left? state)
  (eq? state 'DL))

(define (domino-right? state)
  (eq? state 'DR))

(define (domino-horizontal? state)
  (eq? state 'FL))

(define (domino-vertical? state)
  (eq? state 'FU))

;; grow-aztec: Positive Board[Positive] -> Board[positive]
;; Given an A(size) board state embedded in the middle of board, add empty tiles
;; to produce a partial tiling of A(size+1).
(define (grow-aztec! board size)
  (define embedding (board-size board))
  (when (> size embedding)
    (error "Aztec size must be <= embedding size"))
  (define dim (* 2 embedding))
  (define next-size (add1 size))
  (define border-min (- embedding size))
  (define border-max (+ embedding size))
  (define next-border-min (- embedding next-size))
  (define next-border-max (+ embedding next-size))
  (for* ([row (in-range dim)]
         [col (in-range dim)])
      (cond
        [(or (< row next-border-min) (< col next-border-min)
             (> row next-border-max) (> col next-border-max)) (void)]
        [else
         (define orow (- row border-min))
         (define ocol (- col border-min))
         (define nrow (- row next-border-min))
         (define ncol (- col next-border-min))
         (when (and (in-aztec? next-size nrow ncol) (not (in-aztec? size orow ocol)))
             (board-set! board row col 'EM))])))


;; A(n) pyramids embedded in squares with side length 2n can be given a partial tiling with states like
;;
;; *   'AM for squares outside the A(n) pyramid
;; *   'EM   for squares not covered by a tile, but in the A(n) pyramid
;; *   'DU, 'DD, 'DL, 'DR for a square covered by a domino oriented up/down/left/right,
;;     which represents either the top (if up/down) or left (if left/right) half of the
;;     domino.
;; *   'FU, 'FL if the square is filled by the bottom or right half of another domino,
;;     which is either above or to the left of the F square.
;;     It's likely 'FU vs 'FL is irrelevant, but we distinguish the cases to avoid the need for
;;     any deduction steps to determine which domino it completes.
;;
;; An A(2) pyramid tiling embedded in a 4x4 square can therefore be
;;
;; AM DU FL AM
;; DL DD FL DR
;; FU DU FL FU
;; AM DD FL AM
;;
;; for an up/down/up/down tiling in the middle, sandwiched by left and right dominos.
;;

;; Each A(1) pyramid gets an orientation <- -> for || or ^v for =.
;; From these orientations, each domino moves one step along their vector to open up
;; 2x2 opportunities for more random tiling, with one caveat.


(define (empty-2x2? board row col)
  (and (empty-cell? (board-ref board row col))
       (empty-cell? (board-ref board row (add1 col)))
       (empty-cell? (board-ref board (add1 row) col))
       (empty-cell? (board-ref board (add1 row) (add1 col)))))

(define (empty-2x2! board row col)
  (board-set! board row col 'EM)
  (board-set! board row (add1 col) 'EM)
  (board-set! board (add1 row) col 'EM)
  (board-set! board (add1 row) (add1 col) 'EM))

;; Given the top left of an empty A(1) state, populate with a random 2x2 tiling.
(define (random-2x2-at! board row col)
  (define vertical? (zero? (random 2)))
  (cond [vertical?
         (board-set! board row col 'DU)
         (board-set! board row (add1 col) 'FL)
         (board-set! board (add1 row) col 'DD)
         (board-set! board (add1 row) (add1 col) 'FL)]
        [else
         (board-set! board row col 'DL)
         (board-set! board row (add1 col) 'DR)
         (board-set! board (add1 row) col 'FU)
         (board-set! board (add1 row) (add1 col) 'FU)]))

(define (fill-2x2s! board)
  (define dim (* 2 (board-size board)))
  (for* ([row (in-range (sub1 dim))]
         [col (in-range (sub1 dim))]
         #:when (empty-2x2? board row col))
    (random-2x2-at! board row col)))
  

(define (assert-fill-vertical board row col)
  (unless (domino-vertical? (board-ref board (add1 row) col))
           (error "Fill-domino invariant broken" board row col))
  #t)

(define (assert-fill-horizontal board row col)
  (unless (domino-horizontal? (board-ref board row (add1 col)))
           (error "Fill-domino invariant broken" board row col))
  #t)

;; The caveat is that If we ever have -> <- or v^ adjacent to stop movement, we remove those opposing dominoes.
;; This is apparent if there is ever
;;  *  'DD at row,col and 'DU at row+1,col
;;  *  'DR at row,col and 'DL at row,col+1.
(define (opposition-square? board row col)
  (define tl (board-ref board row col))
  (or
   (and (domino-down? tl)
        (assert-fill-horizontal board row col)
        (domino-up? (board-ref board (add1 row) col))
        (assert-fill-horizontal board (add1 row) col))
   (and (domino-right? tl)
        (assert-fill-vertical board row col)
        (domino-left? (board-ref board row (add1 col)))
        (assert-fill-vertical board row (add1 col)))))

;; Before we can slide any tilings, we must remove all opposing dominoes.
(define (remove-opposition! board)
  (define embedding (board-size board))
  (define dim (* 2 embedding))
  (for* ([row (in-range (sub1 dim))]
         [col (in-range (sub1 dim))]
         #:when (opposition-square? board row col))
    (empty-2x2! board row col)))

;; The board should already be grown and oppositions removed for this procedure to apply.
;; The step happens in two phases to avoid moving the same tile twice accidentally.
;; We walk top->bottom/left->right to move DU and DL dominos, then bottom->top/right->left
;; to move DD and DR dominos. This way we can never visit a moved domino in the orientations
;; we're supposed to step.
(define (step-partial-tiling! board)
  (step-UL-dominos! board)
  (step-DR-dominos! board))

(define (empty-or-FR? board row col)
  (define s (board-ref board row col))
  (or (empty-cell? s)
      (and (domino-vertical? s)
           (domino-right? (board-ref board (sub1 row) col)))))

;; Moving left can be blocked by a soon-to-be-moved downward domino's right half.
(define (empty-or-FD? board row col)
  (define s (board-ref board row col))
  (or (empty-cell? s)
      (and (domino-horizontal? s)
           (domino-down? (board-ref board row (sub1 col))))))

;; PRECONDITION: (domino-up? (board-ref board row col))
(define (move-domino-up! board row col)
  (unless (and (empty-cell? (board-ref board (sub1 row) col))
               (empty-or-FR? board (sub1 row) (add1 col))
               (assert-fill-horizontal board row col))
    (printf "No empty cells to move tile up ~a ~a ~a~%" board row col))
  
  (board-set! board (sub1 row) col 'DU)
  (board-set! board (sub1 row) (add1 col) 'FL)
  (board-set! board row col 'EM)
  (board-set! board row (add1 col) 'EM))

(define (move-domino-down! board row col)
  (unless (and (empty-cell? (board-ref board (add1 row) col))
               (empty-cell? (board-ref board (add1 row) (add1 col))))
    (printf "No empty cells to move tile down ~a ~a ~a~%" board row col))
  (board-set! board (add1 row) col 'DD)
  (board-set! board (add1 row) (add1 col) 'FL)
  (board-set! board row col 'EM)
  ;; The fill square may already have been overwritten by a move left.
  ;; Only if row,col+1 is FL should we empty it.
  (when (domino-horizontal? (board-ref board row (add1 col)))
    (board-set! board row (add1 col) 'EM)))

(define (move-domino-left! board row col)
  (unless (and (empty-cell? (board-ref board row (sub1 col)))
               (empty-or-FD? board row (sub1 col)))
    (printf "No empty cells to move tile left ~a ~a ~a~%" board row col))
  ;; Note that with top->bottom left->right traversal that
  ;; AM EM DL
  ;; EM DL FU
  ;; EM FU
  ;;
  ;; Boards are possible, and that the top DL's matching FU could accidentally
  ;; overwrite the middle DL before it has a chance to move. For these cases,
  ;; we must not overwrite the DL and instead check if we should replace our own
  ;; DL with an FU instead of an EM by checking the square above us (if it exists).
  (board-set! board row (sub1 col) 'DL)
  (unless (domino-left? (board-ref board (add1 row) (sub1 col)))
    (board-set! board (add1 row) (sub1 col) 'FU))
  (define dl-replacement
    (if (and (> row 0) (domino-left? (board-ref board (sub1 row) col)))
        'FU
        'EM))
  (board-set! board row col dl-replacement)
  (board-set! board (add1 row) col 'EM))

(define (move-domino-right! board row col)
  (unless (and (empty-or-FR? board row (add1 col))
               (empty-cell? (board-ref board (add1 row) (add1 col))))
    (printf "No empty cells to move tile right ~a ~a ~a~%" board row col))
  (board-set! board row (add1 col) 'DR)
  (board-set! board (add1 row) (add1 col) 'FU)
  (board-set! board row col 'EM)
  ;; The fill square may already have been overwritten by a move up.
  ;; Only if row+1,col is FU should we empty it.
  (when (domino-vertical? (board-ref board (add1 row) col))
    (board-set! board (add1 row) col 'EM)))

(define (step-UL-dominos! board)
  (define dim (* 2 (board-size board)))
  (for* ([row (in-range (sub1 dim))]
         [col (in-range (sub1 dim))])
    (define state (board-ref board row col))
    (cond [(domino-up? state) (move-domino-up! board row col)]
          [(domino-left? state) (move-domino-left! board row col)])))

(define (step-DR-dominos! board)
  (define dim (* 2 (board-size board)))
  (for* ([row (in-range (sub1 dim) 0 -1)]
         [col (in-range (sub1 dim) 0 -1)])
    (define state (board-ref board row col))
    (cond [(domino-down? state) (move-domino-down! board row col)]
          [(domino-right? state) (move-domino-right! board row col)])))

;; Board[n] Positive -> Void
;; size is the current size of the Aztec pyramid in board.
(define (step-random-aztec-tiling! board size)
  (grow-aztec! board size)
  (remove-opposition! board)
  (step-partial-tiling! board)
  (fill-2x2s! board))

(define (random-aztec-tiling size)
  (define board (empty-board size))
  (define (d b) (pict->bitmap (board->pict b (* size 50))))
  (for/fold ([final #f]) ([step (in-range size)])
    (step-random-aztec-tiling! board step))
  board)

(define (random-aztec-tiling-unfold size)
  (define board (empty-board size))
  (define (d b) (pict->bitmap (board->pict b (* size 50))))
  (define picts
    (for/list ([step (in-range size)])
      (grow-aztec! board step)
      (remove-opposition! board)
      (list (begin (step-partial-tiling! board) (d board))
            (begin (fill-2x2s! board) (d board)))))
  (cons board picts))


;;;;;;;;;;;;;;;;;;
;;
;;;
;;;
;;; DRAWING
;;;
;;
;;
;;;;;;;;;;;;;;;;;;


(define (draw-empty pixels dc x y)
  (send dc set-brush "white" 'transparent)
  (send dc set-pen "black" 1 'solid)
  (send dc draw-rectangle x y pixels pixels))

(define (orientation-color s)
  (match s
    ['DU "blue"]
    ['DD "green"]
    ['DL "yellow"]
    ['DR "red"]
    [_ "black"]))

(define (draw-domino pixels orientation dc x y)
  (send dc set-pen "white" 1 'transparent)
  (send dc set-brush (orientation-color orientation) 'solid)
  (send dc draw-rectangle x y pixels pixels))

(define (draw-vertical pixels above dc x y)
  ;; Set the pen/brush according to whether the square above is legal.
  (match above
    [(or 'DL 'DR) (send dc set-pen "white" 1 'transparent) (send dc set-brush (orientation-color above) 'solid)]
    ['EM (send dc set-pen "red" 1 'dot) (send dc set-brush "orange" 'fdiagonal-hatch)]
    ['AM (send dc set-pen "red" 1 'dash) (send dc set-brush "orange" 'fdiagonal-hatch)]
    ['DU (send dc set-pen "red" 1 'dot-dash) (send dc set-brush "orange" 'cross-hatch)]
    ['DD (send dc set-pen "red" 1 'xor-dot-dash) (send dc set-brush "orange" 'horizontal-hatch)]
    [_ (printf "Unexpected above square ~a~%" above)])
  (send dc draw-rectangle x y pixels pixels))
  
(define (draw-horizontal pixels left dc x y)
  ;; Set the pen/brush according to whether the square to the left is legal.
  (match left
    [(or 'DU 'DD) (send dc set-pen "white" 1 'transparent) (send dc set-brush (orientation-color left) 'solid)]
    ['EM (send dc set-pen "red" 1 'dot) (send dc set-brush "teal" 'fdiagonal-hatch)]
    ['AM (send dc set-pen "red" 1 'dash) (send dc set-brush "teal" 'fdiagonal-hatch)]
    ['DL (send dc set-pen "red" 1 'dot-dash) (send dc set-brush "teal" 'cross-hatch)]
    ['DR  (send dc set-pen "red" 1 'xor-dot-dash) (send dc set-brush "teal" 'horizontal-hatch)]
    [_ (printf "Unexpected left square ~a~%" left)])
  (send dc draw-rectangle x y pixels pixels))

(define (board->pict board pixels)
  (define dim (* 2 (board-size board)))
  (define px-per-sq (/ pixels dim))
  (dc (λ (dc dx dy)
        (define old-brush (send dc get-brush))
        (define old-pen (send dc get-pen))
        (for* ([row (in-range dim)]
               [col (in-range dim)])
          (define x (+ dx (* px-per-sq col)))
          (define y (+ dy (* px-per-sq row)))
          (match (board-ref board row col)
            ['EM (draw-empty px-per-sq dc x y)]
            ['FU (draw-vertical px-per-sq (board-ref board (sub1 row) col) dc x y)]
            ['FL (draw-horizontal px-per-sq (board-ref board row (sub1 col)) dc x y)]
            [(and d (or 'DU 'DD 'DL 'DR)) (draw-domino px-per-sq d dc x y)]
            ['AM (void)]
            [s (printf "Unexpected state ~a~%" s)]))
        (send dc set-brush old-brush)
        (send dc set-pen old-pen))
      pixels pixels))

;; Example
(random-aztec-tiling-unfold 10)
