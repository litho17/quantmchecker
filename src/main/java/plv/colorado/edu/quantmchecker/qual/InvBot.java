package plv.colorado.edu.quantmchecker.qual;

import org.checkerframework.framework.qual.InvisibleQualifier;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.Documented;
import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

/**
 * @author Tianhan Lu
 */
@InvisibleQualifier
@SubtypeOf({Inv.class, Rem.class, InvUnk.class})
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@Documented
// Your type system should include a top qualifier and a bottom qualifier (Section 30.4.7). In most cases, the bottom qualifier should be meta-annotated with @ImplicitFor(literals=LiteralKind.NULL).
// See: KeyForBottom
public @interface InvBot {
}
