;; Agda mode: once `make libraries` (or `make check-scott`) has written
;; _build/libraries, load files with the options of `make check-scott`, so
;; that the Scott-domain files find the TypeTopology of vendor/TypeTopology/.
((agda2-mode
  (eval . (let* ((root (locate-dominating-file default-directory "fpc-compiler.agda-lib"))
                 (libs (and root (expand-file-name "_build/libraries" root))))
            (when (and libs (file-exists-p libs))
              (setq-local agda2-program-args
                          (list (concat "--library-file=" libs)
                                "-l" "standard-library"
                                "-l" "TypeTopology"
                                "-i" (expand-file-name "agda" root)
                                "--safe")))))))
