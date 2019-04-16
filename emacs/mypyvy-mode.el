;;; mypyvy-mode.el --- Major mode for Mypyvy

(defgroup mypyvy nil
  "The Mypyvy system"
  :prefix "mypyvy-"
  :group 'languages)

(defvar mypyvy-mode-hook
  '())

(defcustom mypyvy-program "mypyvy"
  "The path to the mypyvy python script"
  :group 'mypyvy
  :type 'string)

(defvar mypyvy-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c i") 'mypyvy-infer-invariant)
    map)
  "Keymap for Mypyvy major mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.pyv\\'" . mypyvy-mode))

(defun position-of-string (s)
  (save-excursion (search-forward s (line-end-position) 't)))

(defconst mypyvy-keyword-regex
  "\\<\\(modifies\\|sort\\|mutable\\|immutable\\|relation\\|constant\\|function\\|init\\|transition\\|definition\\|invariant\\|axiom\\|old\\|forall\\|exists\\|true\\|false\\|onestate\\|twostate\\|theorem\\|assume\\|automaton\\|global\\|safety\\|phase\\|self\\|derived\\|sketch\\|trace\\|assert\\|any\\|if\\|then\\|else\\|let\\|in\\)\\>")

(defconst mypyvy-font-lock-keywords
  `((,mypyvy-keyword-regex . font-lock-keyword-face)))

(defvar mypyvy-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "w" st)
    (modify-syntax-entry ?# "<" st)
    (modify-syntax-entry ?\n ">" st)
    ; (modify-syntax-entry ?' "w" st)
    st)
  "Syntax table for Mypyvy major mode")

(define-derived-mode mypyvy-mode prog-mode "Mypyvy"
  "Major mode for editing Mypyvy proof files"
  :syntax-table mypyvy-mode-syntax-table
  (set (make-local-variable 'font-lock-defaults) '(mypyvy-font-lock-keywords))
  (font-lock-fontify-buffer)
  (set (make-local-variable 'compile-command)
       (string-join (list "mypyvy verify"
                          (string-join flycheck-mypyvy-args " ")
                          buffer-file-name)
                    " "))
  (local-set-key (kbd "C-c C-c") #'compile))


(defun mypyvy-toggle-flycheck-verify ()
  (interactive)
  (if (equal flycheck-mypyvy-subcommand "verify")
      (set (make-local-variable 'flycheck-mypyvy-subcommand) "typecheck")
    (set (make-local-variable 'flycheck-mypyvy-subcommand) "verify")))

(defun mypyvy-infer-invariant ()
  (interactive)
  (let ((b (generate-new-buffer "*mypyvy-output*")))
    (call-process "mypyvy" nil b t "updr" "--use-z3-unsat-cores" (buffer-file-name))
    (with-current-buffer b
      (goto-char (point-min))
      (if (search-forward "frame is safe and inductive. done!" nil t)
          (progn
            (forward-line)
            (forward-line)
            (delete-region (point-min) (point)))
        (error "could not infer invariant!")))
    (let ((start (point)))
      (insert-buffer-substring-no-properties b)
      (let ((end-marker (point-marker)))
        (goto-char start)
        (cl-loop until (>= (point) (marker-position end-marker))
                 do (insert "invariant ") (forward-line))
        (set-marker end-marker nil)))))



(provide 'mypyvy-mode)
