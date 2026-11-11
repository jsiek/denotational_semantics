;; Agda mode: once `make scott-deps` has fetched TypeTopology, load files
;; with the standard library and TypeTopology, as scott/check.sh does.
((agda2-mode
  (eval . (let* ((root (locate-dominating-file default-directory "denotational.agda-lib"))
                 (libs (and root (expand-file-name "_deps/libraries" root))))
            (when (and libs (file-exists-p libs))
              (setq-local agda2-program-args
                          (list (concat "--library-file=" libs)
                                "-l" "standard-library"
                                "-l" "TypeTopology"
                                "-i" (expand-file-name "agda" root))))))))
