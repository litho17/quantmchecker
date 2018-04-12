package unit;

import org.checkerframework.checker.nullness.qual.*;
import org.checkerframework.*;

public class GetStarted {
	void sample() {
		// @NonNull Object ref = new Object();
		@NonNull Object ref = null;
		A a = new A();
		a.f().g();
	}
}

class A {
	public B f() {
		return new B();
	}
}

class B {
	void g() {}
}
