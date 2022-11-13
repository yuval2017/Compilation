for file in $(ls tests/cases3/*.scm)
do
	echo ------------ testing $file --------
		tests/test_compiler.sh ${file%.scm}
	done