/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package tomcat.org.apache.jasper.el;

import java.lang.reflect.Method;
import java.util.HashMap;
import java.util.Map;

import tomcat.javax.el.ArrayELResolver;
import tomcat.javax.el.BeanELResolver;
import tomcat.javax.el.CompositeELResolver;
import tomcat.javax.el.ELContext;
import tomcat.javax.el.ELManager;
import tomcat.javax.el.ELResolver;
import tomcat.javax.el.ExpressionFactory;
import tomcat.javax.el.FunctionMapper;
import tomcat.javax.el.ListELResolver;
import tomcat.javax.el.MapELResolver;
import tomcat.javax.el.ResourceBundleELResolver;
import tomcat.javax.el.StaticFieldELResolver;
import tomcat.javax.el.ValueExpression;
import tomcat.javax.el.VariableMapper;

import tomcat.org.apache.jasper.Constants;

/**
 * Implementation of ELContext
 *
 * @author Jacob Hookom
 */
public class ELContextImpl extends ELContext {

    private static final FunctionMapper NullFunctionMapper = new FunctionMapper() {
        @Override
        public Method resolveFunction(String prefix, String localName) {
            return null;
        }
    };

    private static final class VariableMapperImpl extends VariableMapper {

        private Map<String, ValueExpression> vars;

        @Override
        public ValueExpression resolveVariable(String variable) {
            if (vars == null) {
                return null;
            }
            return vars.get(variable);
        }

        @Override
        public ValueExpression setVariable(String variable,
                ValueExpression expression) {
            if (vars == null) {
                vars = new HashMap<>();
            }
            if (expression == null) {
                return vars.remove(variable);
            } else {
                return vars.put(variable, expression);
            }
        }
    }

    private static final ELResolver DefaultResolver;

    static {
        if (Constants.IS_SECURITY_ENABLED) {
            DefaultResolver = null;
        } else {
            DefaultResolver = new CompositeELResolver();
            ((CompositeELResolver) DefaultResolver).add(
                    ELManager.getExpressionFactory().getStreamELResolver());
            ((CompositeELResolver) DefaultResolver).add(new StaticFieldELResolver());
            ((CompositeELResolver) DefaultResolver).add(new MapELResolver());
            ((CompositeELResolver) DefaultResolver).add(new ResourceBundleELResolver());
            ((CompositeELResolver) DefaultResolver).add(new ListELResolver());
            ((CompositeELResolver) DefaultResolver).add(new ArrayELResolver());
            ((CompositeELResolver) DefaultResolver).add(new BeanELResolver());
        }
    }

    private final ELResolver resolver;

    private FunctionMapper functionMapper = NullFunctionMapper;

    private VariableMapper variableMapper;

    public ELContextImpl(ExpressionFactory factory) {
        this(getDefaultResolver(factory));
    }

    public ELContextImpl(ELResolver resolver) {
        this.resolver = resolver;
    }

    @Override
    public ELResolver getELResolver() {
        return this.resolver;
    }

    @Override
    public FunctionMapper getFunctionMapper() {
        return this.functionMapper;
    }

    @Override
    public VariableMapper getVariableMapper() {
        if (this.variableMapper == null) {
            this.variableMapper = new VariableMapperImpl();
        }
        return this.variableMapper;
    }

    public void setFunctionMapper(FunctionMapper functionMapper) {
        this.functionMapper = functionMapper;
    }

    public void setVariableMapper(VariableMapper variableMapper) {
        this.variableMapper = variableMapper;
    }

    public static ELResolver getDefaultResolver(ExpressionFactory factory) {
        if (Constants.IS_SECURITY_ENABLED) {
            CompositeELResolver defaultResolver = new CompositeELResolver();
            defaultResolver.add(factory.getStreamELResolver());
            defaultResolver.add(new StaticFieldELResolver());
            defaultResolver.add(new MapELResolver());
            defaultResolver.add(new ResourceBundleELResolver());
            defaultResolver.add(new ListELResolver());
            defaultResolver.add(new ArrayELResolver());
            defaultResolver.add(new BeanELResolver());
            return defaultResolver;
        } else {
            return DefaultResolver;
        }
    }
}
