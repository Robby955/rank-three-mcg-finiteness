PYTHON ?= python3
TEX := manuscript/rank3_genus5_reader.tex
BUILD_DIR := build
SOURCE_DATE_EPOCH ?= 1786665600
SQUARE_TEX := manuscript/general_rank_square_endpoint.tex
SQUARE_BUILD_DIR := build/square-endpoint
SQUARE_SOURCE_DATE_EPOCH ?= 1786320000

.PHONY: build build-square-endpoint verify verify-math verify-release verify-square-endpoint clean clean-square-endpoint

build:
	mkdir -p $(BUILD_DIR)
	SOURCE_DATE_EPOCH=$(SOURCE_DATE_EPOCH) FORCE_SOURCE_DATE=1 \
		latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
		-outdir=$(BUILD_DIR) $(TEX)

build-square-endpoint:
	mkdir -p $(SQUARE_BUILD_DIR)
	SOURCE_DATE_EPOCH=$(SQUARE_SOURCE_DATE_EPOCH) FORCE_SOURCE_DATE=1 \
		latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error \
		-outdir=$(SQUARE_BUILD_DIR) $(SQUARE_TEX)

verify:
	$(PYTHON) verification/verify_release.py

verify-math:
	$(PYTHON) verification/math/verify_hn_branches.py
	$(PYTHON) verification/math/verify_q10_jet.py
	$(PYTHON) verification/math/verify_q9.py

verify-release:
	$(MAKE) verify-math
	$(PYTHON) verification/verify_release.py --compile --pixels
	$(PYTHON) verification/verify_square_endpoint_packet.py --compile

verify-square-endpoint:
	$(PYTHON) verification/verify_square_endpoint_packet.py --compile

clean:
	latexmk -C -outdir=$(BUILD_DIR) $(TEX)

clean-square-endpoint:
	latexmk -C -outdir=$(SQUARE_BUILD_DIR) $(SQUARE_TEX)
