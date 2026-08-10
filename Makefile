PYTHON ?= python3
TEX := manuscript/rank3_genus5_reader.tex
BUILD_DIR := build
SOURCE_DATE_EPOCH ?= 1786320000

.PHONY: build verify verify-math verify-release clean

build:
	mkdir -p $(BUILD_DIR)
	SOURCE_DATE_EPOCH=$(SOURCE_DATE_EPOCH) FORCE_SOURCE_DATE=1 \
		latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
		-outdir=$(BUILD_DIR) $(TEX)

verify:
	$(PYTHON) verification/verify_release.py

verify-math:
	$(PYTHON) verification/math/verify_hn_branches.py
	$(PYTHON) verification/math/verify_q10_jet.py
	$(PYTHON) verification/math/verify_q9.py

verify-release:
	$(MAKE) verify-math
	$(PYTHON) verification/verify_release.py --compile --pixels

clean:
	latexmk -C -outdir=$(BUILD_DIR) $(TEX)
