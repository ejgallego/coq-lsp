(require 'lsp-mode)
(require 'dash)

;; Tell lsp-mode to associate coq-mode with Coq
(push '(coq-mode . "coq") lsp-language-id-configuration)

;; Interfaces used by the proof/goals request of coq-lsp, which prints the
;; current goal.
(lsp-interface
  (coq-lsp:Hyp
    (:names :ty)
    (:def))
  (coq-lsp:Goal
    (:hyps :ty))
  (coq-lsp:GoalConfig
    (:goals :stack :shelf :given_up)
    (:bullet))
  (coq-lsp:Message
    (:level :text)
    (:range))
  (coq-lsp:GoalAnswer
    (:textDocument :position :messages)
    (:goals :error :program)))


(lsp-defun lsp-coq--show-hyp ((&coq-lsp:Hyp :names :ty :def?))
  (--map (insert (format "%s " it)) names)
  (if def? (insert (format ":= %s " def?)))
  (insert (format ": %s\n" ty)))

(defconst lsp-coq--goal-separator (format "%s\n" (make-string 80 ?\u2500))
  "A horizontal ruler to delimit the goal")

(lsp-defun lsp-coq--show-goal ((&coq-lsp:Goal :hyps :ty))
  (--map (lsp-coq--show-hyp it) hyps)
  (insert lsp-coq--goal-separator)
  (insert ty))

(lsp-defun lsp-coq--show-goal-config
  ((&coq-lsp:GoalConfig :goals :stack :shelf :given-up :bullet?))
  (--map (lsp-coq--show-goal it) goals))

(lsp-defun lsp-coq--show-goals
  ((&coq-lsp:GoalAnswer :text-document :position :messages
                        :goals? :error? :program?))
  (if goals?
      (lsp-coq--show-goal-config goals?)
    (message "Not currently in any proof")))

(defun lsp-coq--set-goal-windows ()
  (let* ((coq-goals-buffer (get-buffer-create "*Coq Goals*")))
    (delete-other-windows)
    (split-window-right)
    (other-window 1)
    (switch-to-buffer coq-goals-buffer)
    (erase-buffer)
    (other-window -1)
    coq-goals-buffer))

(defun lsp-coq-proof/goals ()
  "Display the current goals on a separate window."
  (interactive)
  (let* ((coq-goals-buffer (lsp-coq--set-goal-windows))
         (arguments (list :textDocument (lsp--text-document-identifier)
                          :position (lsp--cur-position)
                          :pp_format "Pp"))
         (result (lsp-request "proof/goals" arguments)))
    (with-current-buffer coq-goals-buffer
      (lsp-coq--show-goals result))))

;; Configure lsp-mode to connect to Coq via coq-lsp
(lsp-register-client
  (make-lsp-client :new-connection (lsp-stdio-connection "coq-lsp")
                   :activation-fn (lsp-activate-on "coq")
                   :server-id 'coq-lsp))

(provide 'lsp-coq)
