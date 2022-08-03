.PHONY : build
build:
	pack build jspromises.ipkg

build-tests:
	pack build test/jspromises-test.ipkg

run-tests:
	node test/build/exec/jspromises-test

repl:
	pack --with-ipkg jspromises.ipkg repl src/JSPromise.idr

clean:
	rm -rf ./build

