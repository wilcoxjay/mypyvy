(require 'flycheck)

(flycheck-def-args-var flycheck-mypyvy-args mypyvy)

(defcustom flycheck-mypyvy-subcommand "verify"
  "What subcommand to pass to mypyvy. Good choices are 'verify' or 'typecheck'.")

(make-variable-buffer-local 'flycheck-mypyvy-subcommand)

(flycheck-define-checker mypyvy
  "Mypyvy syntax checker.

Customize `flycheck-mypyvy-args` to add specific args to default
executable."

  :command ("mypyvy"
            (eval flycheck-mypyvy-subcommand)
            (eval flycheck-mypyvy-args)
            source)
  :error-patterns
  ((error line-start "error " (file-name) ":" line ":" column ": " (message) line-end))
  :modes mypyvy-mode)

(add-to-list 'flycheck-checkers 'mypyvy t)

(provide 'flycheck-mypyvy)
;;; flycheck-mypyvy.el ends here
