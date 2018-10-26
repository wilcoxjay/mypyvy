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
    ; (define-key map (kbd "C-c C-c") 'foobar)
    map)
  "Keymap for Mypyvy major mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.pyv\\'" . mypyvy-mode))

(defun position-of-string (s)
  (save-excursion (search-forward s (line-end-position) 't)))

(defconst mypyvy-keyword-regex
  "\\<\\(modifies\\|sort\\|mutable\\|immutable\\|relation\\|constant\\|function\\|init\\|transition\\|invariant\\|axiom\\|old\\|forall\\|exists\\|true\\|false\\|\\|onestate\\|twostate\\|theorem\\)\\>")

(defconst mypyvy-font-lock-keywords
  `((,mypyvy-keyword-regex . font-lock-keyword-face)
    ("#.*" . font-lock-comment-face)))

(defvar mypyvy-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "w" st)
    ; (modify-syntax-entry ?' "w" st)
    st)
  "Syntax table for Mypyvy major mode")

(define-derived-mode mypyvy-mode prog-mode "Mypyvy"
  "Major mode for editing Mypyvy proof files"
  :syntax-table mypyvy-mode-syntax-table
  (set (make-local-variable 'font-lock-defaults) '(mypyvy-font-lock-keywords))
  (font-lock-fontify-buffer))

(provide 'mypyvy-mode)
