;;; duckdb-cube-demo.el --- DuckDB Spatial cube demo -*- lexical-binding: t; -*-

;;; Commentary:

;; Interactive 3D wireframe cube demo using DuckDB's spatial extension for
;; all geometric computations.  Each cube maintains its own DuckDB session,
;; testing the session executor's query latency.
;;
;; DuckDB computes rotation matrices via ST_Affine, applies perspective
;; projection, and returns screen coordinates.  Elisp draws lines between
;; vertices using Bresenham's algorithm, rendering to a Braille character
;; canvas for visual output.
;;
;; Start the demo:
;;
;;     M-x duckdb-cube-start
;;
;; Controls:
;;
;;     +/=     Add cube (new session)
;;     TAB     Cycle to next cube
;;     DEL/-   Remove selected cube
;;     h/l     Rotate or move left/right
;;     j/k     Rotate or move up/down
;;     m       Toggle rotate/move mode
;;     <       Scale down
;;     >       Scale up
;;     a       Toggle auto-rotation
;;     r       Reset selected cube
;;     ?       Open transient menu
;;     q       Quit demo
;;
;; The header displays real-time metrics:
;;
;;     Queries: 1847   | Latency:   3.7ms/cube | Queries/sec: 30
;;
;; Adding cubes increases query throughput linearly - each cube is one
;; session, one query per frame.  With 5 cubes at 30 FPS, the demo
;; sustains 150 queries/second.

;;; Code:

(require 'duckdb-query)
(require 'transient)

(defvar duckdb-cube--buffer "*DuckDB Cube Demo*")
(defvar duckdb-cube--timer nil)
(defvar duckdb-cube--interval 0.033)
(defvar duckdb-cube--old-gc-threshold nil)

;; query/second metrics
(defvar duckdb-cube--recent-query-times nil
  "Ring buffer of recent query timestamps for throughput calculation.")
(defvar duckdb-cube--query-window 2.0
  "Window in seconds for queries/sec calculation.")

;; Per-cube state: ((session angle-x angle-y scale offset-x offset-y edges-cache) ...)
(defvar duckdb-cube--cubes nil)
(defvar duckdb-cube--selected 0)
(defvar duckdb-cube--auto-rotate t)
(defvar duckdb-cube--dirty t)
(defvar duckdb-cube--rendering nil)
(defvar duckdb-cube--frame-times nil)
(defvar duckdb-cube--query-count 0)
(defvar duckdb-cube--start-time nil)
(defvar duckdb-cube--control-mode 'rotate)
(defvar duckdb-cube--cube-counter 0)

;; Canvas
(defvar duckdb-cube--char-width 100)
(defvar duckdb-cube--char-height 35)
(defvar duckdb-cube--pixel-width 200)
(defvar duckdb-cube--pixel-height 140)
(defvar duckdb-cube--canvas nil)
(defvar duckdb-cube--depth-buffer nil)

(defconst duckdb-cube--braille-base #x2800)

(defun duckdb-cube--init-canvas ()
  "Initialize canvas and depth buffer."
  (setq duckdb-cube--pixel-width (* 2 duckdb-cube--char-width)
        duckdb-cube--pixel-height (* 4 duckdb-cube--char-height))
  (setq duckdb-cube--canvas
        (make-bool-vector (* duckdb-cube--pixel-width
                             duckdb-cube--pixel-height) nil))
  (setq duckdb-cube--depth-buffer
        (make-vector (* duckdb-cube--pixel-width
                        duckdb-cube--pixel-height) -999.0)))

(defun duckdb-cube--clear-canvas ()
  "Clear canvas and depth buffer."
  (fillarray duckdb-cube--canvas nil)
  (fillarray duckdb-cube--depth-buffer -999.0))

(defsubst duckdb-cube--pixel-index (x y)
  "Flat index for X,Y."
  (+ x (* y duckdb-cube--pixel-width)))

(defun duckdb-cube--set-pixel (x y depth)
  "Set pixel at X,Y with DEPTH test."
  (when (and (>= x 0) (< x duckdb-cube--pixel-width)
             (>= y 0) (< y duckdb-cube--pixel-height))
    (let ((idx (duckdb-cube--pixel-index x y)))
      (when (> depth (aref duckdb-cube--depth-buffer idx))
        (aset duckdb-cube--canvas idx t)
        (aset duckdb-cube--depth-buffer idx depth)))))

(defun duckdb-cube--draw-line (x1 y1 z1 x2 y2 z2)
  "Draw line from X1,Y1,Z1 to X2,Y2,Z2 with interpolated depth."
  (let* ((dx (abs (- x2 x1)))
         (dy (abs (- y2 y1)))
         (sx (if (< x1 x2) 1 -1))
         (sy (if (< y1 y2) 1 -1))
         (err (- dx dy))
         (x x1) (y y1)
         (steps (max dx dy 1))
         (dz (/ (- z2 z1) (float steps)))
         (z z1))
    (catch 'done
      (while t
        (duckdb-cube--set-pixel x y z)
        (when (and (= x x2) (= y y2))
          (throw 'done nil))
        (let ((e2 (* 2 err)))
          (when (> e2 (- dy))
            (setq err (- err dy) x (+ x sx)))
          (when (< e2 dx)
            (setq err (+ err dx) y (+ y sy))))
        (setq z (+ z dz))))))

(defun duckdb-cube--canvas-to-braille ()
  "Convert pixel buffer to braille string."
  (let ((lines nil)
        (w duckdb-cube--pixel-width))
    (dotimes (char-y duckdb-cube--char-height)
      (let ((line-chars nil)
            (py (* char-y 4)))
        (dotimes (char-x duckdb-cube--char-width)
          (let ((px (* char-x 2))
                (code 0)
                (canvas duckdb-cube--canvas))
            (when (aref canvas (+ px (* py w))) (setq code (logior code #x01)))
            (when (aref canvas (+ (1+ px) (* py w))) (setq code (logior code #x08)))
            (when (aref canvas (+ px (* (+ py 1) w))) (setq code (logior code #x02)))
            (when (aref canvas (+ (1+ px) (* (+ py 1) w))) (setq code (logior code #x10)))
            (when (aref canvas (+ px (* (+ py 2) w))) (setq code (logior code #x04)))
            (when (aref canvas (+ (1+ px) (* (+ py 2) w))) (setq code (logior code #x20)))
            (when (aref canvas (+ px (* (+ py 3) w))) (setq code (logior code #x40)))
            (when (aref canvas (+ (1+ px) (* (+ py 3) w))) (setq code (logior code #x80)))
            (push (+ duckdb-cube--braille-base code) line-chars)))
        (push (concat (nreverse line-chars)) lines)))
    (mapconcat #'identity (nreverse lines) "\n")))

(defun duckdb-cube--init-session (name offset-x offset-y &optional scale)
  "Initialize cube session NAME at OFFSET-X, OFFSET-Y with SCALE."
  (let ((session-name (format "cube-%s" name)))
    (unless (duckdb-query-session-get session-name)
      (duckdb-query-session-start session-name))

    (duckdb-query-with-session session-name
      (duckdb-query "INSTALL spatial; LOAD spatial;")

      (duckdb-query
       "CREATE OR REPLACE TABLE cube_vertices AS
        SELECT * FROM (VALUES
          (0, ST_Point3D(-1, -1, -1)),
          (1, ST_Point3D( 1, -1, -1)),
          (2, ST_Point3D( 1,  1, -1)),
          (3, ST_Point3D(-1,  1, -1)),
          (4, ST_Point3D(-1, -1,  1)),
          (5, ST_Point3D( 1, -1,  1)),
          (6, ST_Point3D( 1,  1,  1)),
          (7, ST_Point3D(-1,  1,  1))
        ) AS t(id, pt)")

      (duckdb-query
       "CREATE OR REPLACE TABLE cube_edges AS
        SELECT * FROM (VALUES
          (0, 1), (1, 2), (2, 3), (3, 0),
          (4, 5), (5, 6), (6, 7), (7, 4),
          (0, 4), (1, 5), (2, 6), (3, 7)
        ) AS t(v1, v2)"))

    (list session-name
          (/ (- (random 100) 50) 50.0)
          (/ (random 628) 100.0)
          (or scale 35.0)
          offset-x
          offset-y
          (duckdb-query-with-session session-name
            (duckdb-query "SELECT v1, v2 FROM cube_edges")))))

(defun duckdb-cube--cube-session (cube) "Session name." (nth 0 cube))
(defun duckdb-cube--cube-angle-x (cube) "X rotation angle." (nth 1 cube))
(defun duckdb-cube--cube-angle-y (cube) "Y rotation angle." (nth 2 cube))
(defun duckdb-cube--cube-scale (cube) "Scale factor." (nth 3 cube))
(defun duckdb-cube--cube-offset-x (cube) "X offset." (nth 4 cube))
(defun duckdb-cube--cube-offset-y (cube) "Y offset." (nth 5 cube))
(defun duckdb-cube--cube-edges (cube) "Cached edge list." (nth 6 cube))

(defun duckdb-cube--set-cube-angle-x (cube val) (setcar (nthcdr 1 cube) val))
(defun duckdb-cube--set-cube-angle-y (cube val) (setcar (nthcdr 2 cube) val))
(defun duckdb-cube--set-cube-scale (cube val) (setcar (nthcdr 3 cube) val))
(defun duckdb-cube--set-cube-offset-x (cube val) (setcar (nthcdr 4 cube) val))
(defun duckdb-cube--set-cube-offset-y (cube val) (setcar (nthcdr 5 cube) val))

(defun duckdb-cube--project-cube (cube)
  "Project CUBE vertices via DuckDB spatial query."
  (let* ((session (duckdb-cube--cube-session cube))
         (angle-x (duckdb-cube--cube-angle-x cube))
         (angle-y (duckdb-cube--cube-angle-y cube))
         (scale (duckdb-cube--cube-scale cube))
         (offset-x (duckdb-cube--cube-offset-x cube))
         (offset-y (duckdb-cube--cube-offset-y cube))
         (center-x (/ duckdb-cube--pixel-width 2))
         (center-y (/ duckdb-cube--pixel-height 2))
         (start-time (current-time)))
    (prog1
        (duckdb-query-with-session session
          (cl-incf duckdb-cube--query-count)
          ;; Record timestamp for sliding window
          (push (current-time) duckdb-cube--recent-query-times)
          (duckdb-query
           (format
            "WITH
             rotated_y AS (
               SELECT id,
                      ST_Affine(pt,
                        cos(%f), 0, sin(%f),
                        0, 1, 0,
                        -sin(%f), 0, cos(%f),
                        0, 0, 0) AS pt
               FROM cube_vertices
             ),
             rotated AS (
               SELECT id,
                      ST_Affine(pt,
                        1, 0, 0,
                        0, cos(%f), -sin(%f),
                        0, sin(%f), cos(%f),
                        0, 0, 0) AS pt
               FROM rotated_y
             ),
             extracted AS (
               SELECT id,
                      ST_X(pt) AS rx,
                      ST_Y(pt) AS ry,
                      ST_Z(pt) AS rz
               FROM rotated
             ),
             projected AS (
               SELECT id,
                      (rx / (rz + 4.0)) * %f + %d AS px,
                      (ry / (rz + 4.0)) * %f + %d AS py,
                      rz AS depth
               FROM extracted
             )
             SELECT id,
                    CAST(px AS INTEGER) AS x,
                    CAST(py AS INTEGER) AS y,
                    depth
             FROM projected
             ORDER BY id"
            angle-y angle-y angle-y angle-y
            angle-x angle-x angle-x angle-x
            scale (+ center-x offset-x)
            scale (+ center-y offset-y))))
      ;; Record frame time for latency display
      (push (* 1000 (float-time (time-subtract (current-time) start-time)))
            duckdb-cube--frame-times)
      (when (> (length duckdb-cube--frame-times) 100)
        (setcdr (nthcdr 98 duckdb-cube--frame-times) nil)))))

(defun duckdb-cube--render ()
  "Render all cubes to buffer."
  (when duckdb-cube--rendering
    (cl-return-from duckdb-cube--render nil))
  (setq duckdb-cube--rendering t)
  (unwind-protect
      (progn
        (duckdb-cube--clear-canvas)

        (let ((num-cubes (length duckdb-cube--cubes)))
          (dotimes (i num-cubes)
            (let* ((cube (nth i duckdb-cube--cubes))
                   (vertices (duckdb-cube--project-cube cube))
                   (edges (duckdb-cube--cube-edges cube))
                   (selected (= i duckdb-cube--selected)))

              (dolist (edge edges)
                (let* ((v1-id (cdr (assq 'v1 edge)))
                       (v2-id (cdr (assq 'v2 edge)))
                       (v1 (nth v1-id vertices))
                       (v2 (nth v2-id vertices)))
                  (duckdb-cube--draw-line
                   (cdr (assq 'x v1)) (cdr (assq 'y v1)) (cdr (assq 'depth v1))
                   (cdr (assq 'x v2)) (cdr (assq 'y v2)) (cdr (assq 'depth v2)))))

              (when selected
                (dolist (v vertices)
                  (let ((x (cdr (assq 'x v)))
                        (y (cdr (assq 'y v)))
                        (z (cdr (assq 'depth v))))
                    (duckdb-cube--set-pixel (- x 1) y z)
                    (duckdb-cube--set-pixel (+ x 1) y z)
                    (duckdb-cube--set-pixel x (- y 1) z)
                    (duckdb-cube--set-pixel x (+ y 1) z)
                    (duckdb-cube--set-pixel (- x 2) y z)
                    (duckdb-cube--set-pixel (+ x 2) y z))))))

          ;; Trim old query timestamps outside window
          (let ((now (current-time))
                (cutoff (* 2 duckdb-cube--query-window)))
            (setq duckdb-cube--recent-query-times
                  (seq-filter (lambda (ts)
                                (< (float-time (time-subtract now ts)) cutoff))
                              duckdb-cube--recent-query-times)))

          ;; Calculate queries/sec from sliding window
          (let* ((now (current-time))
                 (recent-count (length (seq-filter
                                        (lambda (ts)
                                          (< (float-time (time-subtract now ts))
                                             duckdb-cube--query-window))
                                        duckdb-cube--recent-query-times)))
                 (queries-per-sec (/ recent-count duckdb-cube--query-window))
                 (avg-ms (if duckdb-cube--frame-times
                             (/ (apply #'+ duckdb-cube--frame-times)
                                (float (length duckdb-cube--frame-times)))
                           0))
                 (per-cube-ms (/ avg-ms (max 1 num-cubes)))
                 (braille (duckdb-cube--canvas-to-braille))
                 (cube (nth duckdb-cube--selected duckdb-cube--cubes)))

            (with-current-buffer (get-buffer-create duckdb-cube--buffer)
              (let ((inhibit-read-only t)
                    (inhibit-modification-hooks t))
                (erase-buffer)
               (let ((title (format "DuckDB Spatial Cube Demo - %d Cube%s, %d Session%s"
                                     num-cubes (if (= num-cubes 1) "" "s")
                                     num-cubes (if (= num-cubes 1) "" "s")))
                      (stats (format "Queries: %-6d | Latency: %5.1fms/cube | Queries/sec: %.0f"
                                     duckdb-cube--query-count per-cube-ms queries-per-sec))
                      (info (format "Selected: [%d/%d] Pos:(%+d,%+d) Scale:%.0f | Mode: %s | Auto: %s"
                                    (1+ duckdb-cube--selected) num-cubes
                                    (truncate (duckdb-cube--cube-offset-x cube))
                                    (truncate (duckdb-cube--cube-offset-y cube))
                                    (duckdb-cube--cube-scale cube)
                                    (upcase (symbol-name duckdb-cube--control-mode))
                                    (if duckdb-cube--auto-rotate "ON" "OFF")))
                      (help "[+] Add | [TAB] Next | [DEL] Remove | [m] Mode | [?] Menu | [q] Quit"))
                  (insert (propertize title 'face '(:height 1.4 :weight bold)) "\n")
                  (insert (propertize stats 'face '(:height 1.4 :weight bold)) "\n")
                  (insert (propertize info 'face '(:height 1.1)) "\n")
                  (insert (propertize help 'face '(:height 1.0 :slant italic)) "\n"))
                (insert braille))))))
    (setq duckdb-cube--rendering nil
          duckdb-cube--dirty nil)))

(defun duckdb-cube--tick ()
  "Animation tick."
  (when duckdb-cube--auto-rotate
    (let ((num-cubes (length duckdb-cube--cubes)))
      (dotimes (i num-cubes)
        (let* ((cube (nth i duckdb-cube--cubes))
               (speed (+ 0.02 (* i 0.008))))
          (duckdb-cube--set-cube-angle-y
           cube (+ (duckdb-cube--cube-angle-y cube) speed))
          (when (> (duckdb-cube--cube-angle-y cube) (* 2 float-pi))
            (duckdb-cube--set-cube-angle-y cube 0.0)))))
    (setq duckdb-cube--dirty t))

  (when (and duckdb-cube--dirty (not duckdb-cube--rendering))
    (condition-case err
        (duckdb-cube--render)
      (error (message "Render error: %s" err)))))

;;; Interactive Commands

(defun duckdb-cube-next ()
  "Select next cube."
  (interactive)
  (setq duckdb-cube--selected
        (mod (1+ duckdb-cube--selected) (length duckdb-cube--cubes)))
  (setq duckdb-cube--dirty t)
  (message "Selected cube %d/%d"
           (1+ duckdb-cube--selected) (length duckdb-cube--cubes)))

(defun duckdb-cube-add ()
  "Add a new cube with its own session."
  (interactive)
  (cl-incf duckdb-cube--cube-counter)
  (let* ((offset-x (- (random 120) 60))
         (offset-y (- (random 80) 40))
         (scale (+ 20.0 (random 20)))
         (new-cube (duckdb-cube--init-session
                    (format "dyn-%d" duckdb-cube--cube-counter)
                    offset-x offset-y scale)))
    (setq duckdb-cube--cubes (append duckdb-cube--cubes (list new-cube)))
    (setq duckdb-cube--selected (1- (length duckdb-cube--cubes)))
    (setq duckdb-cube--dirty t)
    (message "Added cube %d (%d sessions)"
             (length duckdb-cube--cubes)
             (length duckdb-cube--cubes))))

(defun duckdb-cube-remove ()
  "Remove selected cube and its session."
  (interactive)
  (when (> (length duckdb-cube--cubes) 1)
    (let* ((cube (nth duckdb-cube--selected duckdb-cube--cubes))
           (session (duckdb-cube--cube-session cube)))
      (ignore-errors (duckdb-query-session-kill session))
      (setq duckdb-cube--cubes (delq cube duckdb-cube--cubes))
      (setq duckdb-cube--selected
            (min duckdb-cube--selected (1- (length duckdb-cube--cubes))))
      (setq duckdb-cube--dirty t)
      (message "Removed cube (%d remaining)" (length duckdb-cube--cubes)))))

(defun duckdb-cube-toggle-mode ()
  "Toggle between rotate and move mode."
  (interactive)
  (setq duckdb-cube--control-mode
        (if (eq duckdb-cube--control-mode 'rotate) 'move 'rotate))
  (setq duckdb-cube--dirty t)
  (message "Control mode: %s" (upcase (symbol-name duckdb-cube--control-mode))))

(defun duckdb-cube-left ()
  "Rotate or move selected cube left."
  (interactive)
  (let ((cube (nth duckdb-cube--selected duckdb-cube--cubes)))
    (if (eq duckdb-cube--control-mode 'rotate)
        (duckdb-cube--set-cube-angle-y
         cube (- (duckdb-cube--cube-angle-y cube) 0.15))
      (duckdb-cube--set-cube-offset-x
       cube (- (duckdb-cube--cube-offset-x cube) 8))))
  (setq duckdb-cube--dirty t))

(defun duckdb-cube-right ()
  "Rotate or move selected cube right."
  (interactive)
  (let ((cube (nth duckdb-cube--selected duckdb-cube--cubes)))
    (if (eq duckdb-cube--control-mode 'rotate)
        (duckdb-cube--set-cube-angle-y
         cube (+ (duckdb-cube--cube-angle-y cube) 0.15))
      (duckdb-cube--set-cube-offset-x
       cube (+ (duckdb-cube--cube-offset-x cube) 8))))
  (setq duckdb-cube--dirty t))

(defun duckdb-cube-up ()
  "Rotate or move selected cube up."
  (interactive)
  (let ((cube (nth duckdb-cube--selected duckdb-cube--cubes)))
    (if (eq duckdb-cube--control-mode 'rotate)
        (duckdb-cube--set-cube-angle-x
         cube (- (duckdb-cube--cube-angle-x cube) 0.15))
      (duckdb-cube--set-cube-offset-y
       cube (- (duckdb-cube--cube-offset-y cube) 8))))
  (setq duckdb-cube--dirty t))

(defun duckdb-cube-down ()
  "Rotate or move selected cube down."
  (interactive)
  (let ((cube (nth duckdb-cube--selected duckdb-cube--cubes)))
    (if (eq duckdb-cube--control-mode 'rotate)
        (duckdb-cube--set-cube-angle-x
         cube (+ (duckdb-cube--cube-angle-x cube) 0.15))
      (duckdb-cube--set-cube-offset-y
       cube (+ (duckdb-cube--cube-offset-y cube) 8))))
  (setq duckdb-cube--dirty t))

(defun duckdb-cube-scale-up ()
  "Increase selected cube scale."
  (interactive)
  (let ((cube (nth duckdb-cube--selected duckdb-cube--cubes)))
    (duckdb-cube--set-cube-scale cube (min 80.0 (+ (duckdb-cube--cube-scale cube) 5.0))))
  (setq duckdb-cube--dirty t))

(defun duckdb-cube-scale-down ()
  "Decrease selected cube scale."
  (interactive)
  (let ((cube (nth duckdb-cube--selected duckdb-cube--cubes)))
    (duckdb-cube--set-cube-scale cube (max 10.0 (- (duckdb-cube--cube-scale cube) 5.0))))
  (setq duckdb-cube--dirty t))

(defun duckdb-cube-toggle-auto ()
  "Toggle auto-rotation."
  (interactive)
  (setq duckdb-cube--auto-rotate (not duckdb-cube--auto-rotate))
  (unless duckdb-cube--auto-rotate
    (setq duckdb-cube--dirty t))
  (message "Auto-rotate: %s" (if duckdb-cube--auto-rotate "ON" "OFF")))

(defun duckdb-cube-reset ()
  "Reset selected cube position and rotation."
  (interactive)
  (let ((cube (nth duckdb-cube--selected duckdb-cube--cubes)))
    (duckdb-cube--set-cube-angle-x cube 0.3)
    (duckdb-cube--set-cube-angle-y cube 0.0)
    (duckdb-cube--set-cube-offset-x cube 0)
    (duckdb-cube--set-cube-offset-y cube 0)
    (duckdb-cube--set-cube-scale cube 35.0))
  (setq duckdb-cube--dirty t))

(defun duckdb-cube--cleanup-sessions ()
  "Kill all cube sessions."
  (dolist (cube duckdb-cube--cubes)
    (ignore-errors (duckdb-query-session-kill (duckdb-cube--cube-session cube))))
  (setq duckdb-cube--cubes nil))

(defun duckdb-cube-stop ()
  "Stop cube demo and clean up."
  (interactive)
  (when duckdb-cube--timer
    (cancel-timer duckdb-cube--timer)
    (setq duckdb-cube--timer nil))
  (when duckdb-cube--old-gc-threshold
    (setq gc-cons-threshold duckdb-cube--old-gc-threshold))
  (let* ((num-cubes (length duckdb-cube--cubes))
         (now (current-time))
         (recent-count (length (seq-filter
                                (lambda (ts)
                                  (< (float-time (time-subtract now ts))
                                     duckdb-cube--query-window))
                                duckdb-cube--recent-query-times)))
         (queries-per-sec (/ recent-count duckdb-cube--query-window)))
    (duckdb-cube--cleanup-sessions)
    (message "Stopped. %d queries across %d session%s (%.0f queries/sec at exit)"
             duckdb-cube--query-count num-cubes (if (= num-cubes 1) "" "s")
             queries-per-sec)))

;;; Transient Menu

(transient-define-prefix duckdb-cube-menu ()
  "Cube demo controls."
  :transient-suffix 'transient--do-stay
  ["DuckDB Spatial Cube Demo"
   ["Cubes"
    ("+" "Add cube" duckdb-cube-add)
    ("TAB" "Next cube" duckdb-cube-next)
    ("DEL" "Remove cube" duckdb-cube-remove)]
   ["Control"
    ("m" "Toggle mode" duckdb-cube-toggle-mode)
    ("h" "Left" duckdb-cube-left)
    ("l" "Right" duckdb-cube-right)
    ("k" "Up" duckdb-cube-up)
    ("j" "Down" duckdb-cube-down)
    ("r" "Reset" duckdb-cube-reset)]
   ["Scale"
    (">" "Bigger" duckdb-cube-scale-up)
    ("<" "Smaller" duckdb-cube-scale-down)]
   ["Animation"
    ("a" "Toggle auto" duckdb-cube-toggle-auto)]
   ["Session"
    ("q" "Quit" duckdb-cube-stop :transient nil)]])

;;;###autoload
(defun duckdb-cube-start ()
  "Start the DuckDB spatial cube demo."
  (interactive)
  (setq duckdb-cube--frame-times nil
        duckdb-cube--recent-query-times nil  ; Reset sliding window
        duckdb-cube--query-count 0
        duckdb-cube--start-time (current-time)
        duckdb-cube--auto-rotate t
        duckdb-cube--dirty t
        duckdb-cube--rendering nil
        duckdb-cube--selected 0
        duckdb-cube--control-mode 'rotate
        duckdb-cube--cube-counter 0)

  (setq duckdb-cube--cubes
        (list (duckdb-cube--init-session "main" 0 0 40.0)))

  (duckdb-cube--init-canvas)

  (setq duckdb-cube--old-gc-threshold gc-cons-threshold)
  (setq gc-cons-threshold (* 100 1024 1024))

  (duckdb-cube--render)
  (pop-to-buffer duckdb-cube--buffer)
  (setq duckdb-cube--timer
        (run-with-timer 0 duckdb-cube--interval #'duckdb-cube--tick))

  (with-current-buffer duckdb-cube--buffer
    (use-local-map (make-sparse-keymap))
    (local-set-key "?" #'duckdb-cube-menu)
    (local-set-key "q" #'duckdb-cube-stop)
    (local-set-key "+" #'duckdb-cube-add)
    (local-set-key "=" #'duckdb-cube-add)
    (local-set-key "\t" #'duckdb-cube-next)
    (local-set-key (kbd "DEL") #'duckdb-cube-remove)
    (local-set-key "-" #'duckdb-cube-remove)
    (local-set-key "m" #'duckdb-cube-toggle-mode)
    (local-set-key "h" #'duckdb-cube-left)
    (local-set-key "l" #'duckdb-cube-right)
    (local-set-key "k" #'duckdb-cube-up)
    (local-set-key "j" #'duckdb-cube-down)
    (local-set-key "a" #'duckdb-cube-toggle-auto)
    (local-set-key "r" #'duckdb-cube-reset)
    (local-set-key ">" #'duckdb-cube-scale-up)
    (local-set-key "<" #'duckdb-cube-scale-down)))

(provide 'duckdb-cube-demo)

;;; duckdb-cube-demo.el ends here
