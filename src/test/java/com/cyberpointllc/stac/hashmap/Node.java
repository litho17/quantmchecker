package com.cyberpointllc.stac.hashmap;

import java.util.Map;

/**
 * Basic hash bin node, used for most entries.  (See below for
 * TreeNode subclass, and in LinkedHashMap for its Entry subclass.)
 */
class Node<K, V> implements Map.Entry<K, V> {

    final int hash;

    final K key;

    V value;

    Node<K, V> next;

    Node(int hash, K key, V value, Node<K, V> next) {
        this.hash = hash;
        this.key = key;
        this.value = value;
        this.next = next;
    }

    public final K getKey() {
        return key;
    }

    public final V getValue() {
        return value;
    }

    public final String toString() {
        return key + "=" + value;
    }

    /*public final int hashCode() {
        return Objects.hashCode(key) ^ Objects.hashCode(value);
    }*/
    public final V setValue(V newValue) {
        V oldValue = value;
        value = newValue;
        return oldValue;
    }

    public final boolean equals(Object o) {
        if (o == this)
            return true;
        if (o instanceof Map.Entry) {
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            /*if (Objects.equals(key, e.getKey()) &&
                Objects.equals(value, e.getValue()))
                return true;*/
            if (key.equals(e.getKey()) && value.equals(e.getValue()))
                return true;
        }
        return false;
    }

    public static int hash(Object key, int capacity) {
        return (key.hashCode() & 0x7fffffff) % capacity;
    }
}
