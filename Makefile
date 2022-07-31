.PHONY : build
build:
	pack build jspromises.ipkg

repl:
	pack --with-ipkg jspromises.ipkg repl src/JSPromise.idr

clean:
	rm -rf ./build

