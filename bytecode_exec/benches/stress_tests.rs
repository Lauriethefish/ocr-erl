use criterion::{black_box, criterion_group, criterion_main, Criterion};
use erl_bytecode_exec::executor;
use erl_bytecode_exec::stdlib::Value;

macro_rules! exec_bench {
    ($bench_name:ident,
     id: $id:expr,
     code: $code:expr,
     func: $func:expr,
     args: $args:expr,
     expected_result: $expected:expr) => {
        fn $bench_name(c: &mut Criterion) {
            let ast = erl_parser::parse_from_string($code).unwrap();
            let module = erl_bytecode_exec::compiler::compile(ast);
            let routine = || executor::execute_by_name(&module, $func, black_box($args));
            assert_eq!($expected, routine().unwrap());

            c.bench_function($id, |b| b.iter(routine));
        }
    };
}

exec_bench!(bench_primes,
    id: "number of primes from 1 to 100",
    code: "
    function primes(upTo)
        primes = 0
        for n = 1 to upTo
            factors = 0
            for pot_fac = 1 to n
                if n MOD pot_fac == 0 then
                    factors = factors + 1
                endif
            next pot_fac

            if factors == 2 then
                primes = primes + 1
            endif
        next n

        return primes
    endfunction
    ",
    func: "primes",
    args: &[Value::Integer(100)],
    expected_result: Some(Value::Integer(25))
);

exec_bench!(bench_sum,
    id: "sum of all integers from 1 to 4000",
    code: "
    function sum(upTo)
        total = 0
        i = 1
        while i <= upTo
            total = total + i
            i = i + 1
        endwhile

        return total
    endfunction
    ",
    func: "sum",
    args: &[Value::Integer(4000)],
    expected_result: Some(Value::Integer(8002000))
);

exec_bench!(bench_collatz,
    id: "verifying collatz conjecture for integers from 1 to 100",
    code: "
    procedure verify(upTo)
        for i = 1 to upTo
            current = i
            while current != 1
                if (current MOD 2) == 0 then
                    current = current DIV 2
                else
                    current = (current * 3) + 1
                endif
            endwhile
        next i
    endprocedure
    ",
    func: "verify",
    args: &[Value::Integer(100)],
    expected_result: None
);

exec_bench!(bench_fibonacci,
    id: "find 92nd number in the fibonacci sequence",
    code: "
    function fibonacci(n)
        a = 1
        b = 1
        for i = 2 to n
            after = a + b
            a = b
            b = after
        next i

        return a
    endfunction
    ",
    func: "fibonacci",
    args: &[Value::Integer(92)],
    expected_result: Some(Value::Integer(7540113804746346429))
);

criterion_group!(
    benches,
    bench_primes,
    bench_sum,
    bench_collatz,
    bench_fibonacci
);
criterion_main!(benches);
