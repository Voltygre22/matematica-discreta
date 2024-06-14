import java.lang.AssertionError;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes annotats amb "// TODO". L'enunciat de
 * cada un d'ells és al comentari de la seva signatura i exemples del seu funcionament als mètodes
 * `Tema1.tests`, `Tema2.tests`, etc.
 *
 * L'avaluació consistirà en:
 *
 * - Si el codi no compila, la nota del grup serà un 0.
 *
 * - Si heu fet cap modificació que no sigui afegir un mètode, afegir proves als mètodes "tests()" o
 *   implementar els mètodes annotats amb "// TODO", la nota del grup serà un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implemnetats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Algunes
 *   consideracions importants:
 *    + Entregau amb la mateixa codificació (UTF-8) i finals de línia (LF, no CR+LF)
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau a continuació els vostres noms i entregau únicament aquest fitxer.
 * - Nom 1:
 * - Nom 2:
 * - Nom 3:
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat i vos recomanam que treballeu amb un fork d'aquest repositori per seguir més
 * fàcilment les actualitzacions amb enunciats nous. Si no podeu visualitzar bé algun enunciat,
 * assegurau-vos de que el vostre editor de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {
  /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
   *
   * La majoria dels mètodes reben de paràmetre l'univers (representat com un array) i els predicats
   * adients (per exemple, `Predicate<Integer> p`). Per avaluar aquest predicat, si `x` és un
   * element de l'univers, podeu fer-ho com `p.test(x)`, que té com resultat un booleà (true si
   * `P(x)` és cert). Els predicats de dues variables són de tipus `BiPredicate<Integer, Integer>` i
   * similarment s'avaluen com `p.test(x, y)`.
   *
   * En cada un d'aquests exercicis (excepte el primer) us demanam que donat l'univers i els
   * predicats retorneu `true` o `false` segons si la proposició donada és certa (suposau que
   * l'univers és suficientment petit com per poder provar tots els casos que faci falta).
   */
  static class Tema1 {
    /*
     * Donat n > 1, en quants de casos (segons els valors de veritat de les proposicions p1,...,pn)
     * la proposició (...((p1 -> p2) -> p3) -> ...) -> pn és certa?
     *
     * Vegeu el mètode Tema1.tests() per exemples.
     */
    static int exercici1(int n) {
    // Base case
      if (n <= 1) return 0;

    // There are 2^n combinations of p1, p2, ..., pn
      int totalCombinations = (1 << n); // This is 2^n
    
    // The number of combinations where the last proposition pn is true is 2^(n-1)
      int truePnCombinations = (1 << (n - 1)); // This is 2^(n-1)
    
    // Return the number of cases where the entire proposition is true
      return totalCombinations - truePnCombinations;
    }

    /*
     * És cert que ∀x : P(x) -> ∃!y : Q(x,y) ?
     */
    static boolean exercici2(int[] universe, Predicate<Integer> p, BiPredicate<Integer, Integer> q) {
      for (int x : universe) {
        if (p.test(x)) { // If P(x) is true
            int count = 0;
            for (int y : universe) {
                if (q.test(x, y)) {
                    count++;
                }
            }
            if (count != 1) { // There must be exactly one y such that Q(x, y) is true
                return false;
            }
        }
    }
    return true; // All elements satisfied the condition

    /*
     * És cert que ∃x : ∀y : Q(x, y) -> P(x) ?
     */
      static boolean exercici3(int[] universe, Predicate<Integer> p, BiPredicate<Integer, Integer> q) {
        for (int x : universe) {
          boolean validForAllY = true;
          for (int y : universe) {
            if (q.test(x, y) && !p.test(x)) {
                validForAllY = false;
                break;
            }
          }
          if (validForAllY) {
            return true;
          }
        }
        return false;
      }

    /*
     * És cert que ∃x : ∃!y : ∀z : P(x,z) <-> Q(y,z) ?
     */
  static boolean exercici4(int[] universe, BiPredicate<Integer, Integer> p, BiPredicate<Integer, Integer> q) {
    for (int x : universe) {
        int validYCount = 0;
        for (int y : universe) {
            boolean validForAllZ = true;
            for (int z : universe) {
                if (p.test(x, z) != q.test(y, z)) {
                    validForAllZ = false;
                    break;
                }
            }
            if (validForAllZ) {
                validYCount++;
                if (validYCount > 1) {
                    break;
                }
            }
        }
        if (validYCount == 1) {
            return true;
        }
    }
    return false;
}

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1

      // p1 -> p2 és cert exactament a 3 files
      // p1 p2
      // 0  0  <-
      // 0  1  <-
      // 1  0
      // 1  1  <-
      assertThat(exercici1(2) == 3);

      // (p1 -> p2) -> p3 és cert exactament a 5 files
      // p1 p2 p3
      // 0  0  0
      // 0  0  1  <-
      // 0  1  0
      // 0  1  1  <-
      // 1  0  0  <-
      // 1  0  1  <-
      // 1  1  0
      // 1  1  1  <-
      assertThat(exercici1(3) == 5);

      // Exercici 2
      // ∀x : P(x) -> ∃!y : Q(x,y)
      assertThat(
          exercici2(
            new int[] { 1, 2, 3 },
            x -> x % 2 == 0,
            (x, y) -> x+y >= 5
          )
      );

      assertThat(
          !exercici2(
            new int[] { 1, 2, 3 },
            x -> x < 3,
            (x, y) -> x-y > 0
          )
      );

      // Exercici 3
      // És cert que ∃x : ∀y : Q(x, y) -> P(x) ?
      assertThat(
          exercici3(
            new int[] { 1, 2, 3, 4, 5, 6, 7, 8, 9 },
            x -> x % 3 != 0,
            (x, y) -> y % x == 0
          )
      );

      assertThat(
          exercici3(
            new int[] { 1, 2, 3, 4, 5, 6, 7, 8, 9 },
            x -> x % 4 != 0,
            (x, y) -> (x*y) % 4 != 0
          )
      );

      // Exercici 4
      // És cert que ∃x : ∃!y : ∀z : P(x,z) <-> Q(y,z) ?
      assertThat(
          exercici4(
            new int[] { 0, 1, 2, 3, 4, 5 },
            (x, z) -> x*z == 1,
            (y, z) -> y*z == 2
          )
      );

      assertThat(
          !exercici4(
            new int[] { 2, 3, 4, 5 },
            (x, z) -> x*z == 1,
            (y, z) -> y*z == 2
          )
      );
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][].
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a, el
   * codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per aplicar
   * f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu f.apply(x).
   */
  }
  static class Tema2 {
    /*
     * Calculau el nombre d'elements del conjunt de parts de (a u b) × (a \ c)
     *
     * Podeu soposar que `a`, `b` i `c` estan ordenats de menor a major.
     */
    static int exercici1(int[] a, int[] b, int[] c) {
    // Step 1: Compute A ∪ B
      int[] unionArray = new int[a.length + b.length];
      int unionSize = 0;

    // Add elements of a to unionArray
      for (int i = 0; i < a.length; i++) {
        if (!contains(unionArray, unionSize, a[i])) {
            unionArray[unionSize++] = a[i];
        }
      }

    // Add elements of b to unionArray
      for (int i = 0; i < b.length; i++) {
        if (!contains(unionArray, unionSize, b[i])) {
            unionArray[unionSize++] = b[i];
        }
      }

    // Step 2: Compute A \ C
      int[] differenceArray = new int[a.length];
      int differenceSize = 0;

      for (int i = 0; i < a.length; i++) {
        if (!contains(c, c.length, a[i])) {
            differenceArray[differenceSize++] = a[i];
        }
      }

    // Step 3: Form the Cartesian Product (A ∪ B) × (A \ C)
      int cartesianProductSize = unionSize * differenceSize;

    // Step 4: Calculate the size of the power set
      return (int) Math.pow(2, cartesianProductSize);
    }

// Helper method to check if an array contains an element up to a given size
    static boolean contains(int[] array, int size, int value) {
      for (int i = 0; i < size; i++) {
        if (array[i] == value) {
          return true;
        }
      }
      return false;
    }

    /*
     * La clausura d'equivalència d'una relació és el resultat de fer-hi la clausura reflexiva, simètrica i
     * transitiva simultàniament, i, per tant, sempre és una relació d'equivalència.
     *
     * Trobau el cardinal d'aquesta clausura.
     *
     * Podeu soposar que `a` i `rel` estan ordenats de menor a major (`rel` lexicogràficament).
     */
    static int exercici2(int[] a, int[][] rel) {
    // Step 1: Convert the given relation to a list of pairs
      List<Pair> relation = new ArrayList<>();
      for (int[] pair : rel) {
        addPair(relation, pair[0], pair[1]);
      }

    // Step 2: Reflexive closure: Add (x, x) for all x in a
      for (int x : a) {
        addPair(relation, x, x);
      }

    // Step 3: Symmetric closure: Add (y, x) for all (x, y)
      int currentSize = relation.size();
      for (int i = 0; i < currentSize; i++) {
        Pair pair = relation.get(i);
        addPair(relation, pair.second, pair.first);
      }

    // Step 4: Transitive closure: Add (x, z) for all (x, y) and (y, z)
      boolean added;
      do {
        added = false;
        int initialSize = relation.size();
        List<Pair> newPairs = new ArrayList<>();
        for (int i = 0; i < initialSize; i++) {
            for (int j = 0; j < initialSize; j++) {
                Pair p1 = relation.get(i);
                Pair p2 = relation.get(j);
                if (p1.second == p2.first) {
                    if (addPair(newPairs, p1.first, p2.second)) {
                        added = true;
                    }
                }
            }
        }
        relation.addAll(newPairs);
      } while (added);

    // Step 5: The size of the relation list is the cardinality of the equivalence closure
      return relation.size();
    }

// Helper method to add a pair to the list if it doesn't already exist
    static boolean addPair(List<Pair> relation, int first, int second) {
      for (Pair pair : relation) {
        if (pair.first == first && pair.second == second) {
            return false;
        }
      }
      relation.add(new Pair(first, second));
      return true;
    }

// Helper class to represent pairs
    static class Pair {
      int first;
      int second;

      Pair(int first, int second) {
        this.first = first;
        this.second = second;
      }
    }

    /*
     * Comprovau si la relació `rel` és un ordre total sobre `a`. Si ho és retornau el nombre
     * d'arestes del seu diagrama de Hasse. Sino, retornau -2.
     *
     * Podeu soposar que `a` i `rel` estan ordenats de menor a major (`rel` lexicogràficament).
     */
    static int exercici3(int[] a, int[][] rel) {
      int n = a.length;
      boolean[][] relation = new boolean[n][n];
      
    // Fill the relation matrix
      for (int[] pair : rel) {
        relation[pair[0]][pair[1]] = true;
      }

    // Check reflexivity
      for (int i = 0; i < n; i++) {
        if (!relation[i][i]) return -2;
      }

    // Check antisymmetry and totality
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
          if (i != j) {
            if (relation[i][j] && relation[j][i]) return -2;
            if (!relation[i][j] && !relation[j][i]) return -2;
          }
        }
      }

    // Check transitivity
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
          for (int k = 0; k < n; k++) {
            if (relation[i][j] && relation[j][k] && !relation[i][k]) return -2;
          }
        }
      }

    // Calculate Hasse diagram edges (remove reflexive and transitive edges)
      int hasseEdges = 0;
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
          if (i != j && relation[i][j]) {
            boolean isTransitive = false;
            for (int k = 0; k < n; k++) {
              if (k != i && k != j && relation[i][k] && relation[k][j]) {
                isTransitive = true;
                break;
              }
            }
            if (!isTransitive) {
              hasseEdges++;
            }
          }
        }
      }
      return hasseEdges;
    }



    /*
     * Comprovau si les relacions `rel1` i `rel2` són els grafs de funcions amb domini i codomini
     * `a`. Si ho son, retornau el graf de la composició `rel2 ∘ rel1`. Sino, retornau null.
     *
     * Podeu soposar que `a`, `rel1` i `rel2` estan ordenats de menor a major (les relacions,
     * lexicogràficament).
     */
    static int[][] exercici4(int[] a, int[][] rel1, int[][] rel2) {
      int n = a.length;

    // Check if rel1 is a function
      boolean[] domainRel1 = new boolean[n];
      for (int[] pair : rel1) {
        int x = pair[0];
        if (domainRel1[x]) return null; // rel1 is not a function
        domainRel1[x] = true;
      }

    // Check if rel2 is a function
      boolean[] domainRel2 = new boolean[n];
      for (int[] pair : rel2) {
        int x = pair[0];
        if (domainRel2[x]) return null; // rel2 is not a function
        domainRel2[x] = true;
      }

    // Calculate the composition rel2 ∘ rel1
      ArrayList<int[]> composition = new ArrayList<>();
      for (int[] pair1 : rel1) {
        int x = pair1[0];
        int y = pair1[1];
        for (int[] pair2 : rel2) {
            if (pair2[0] == y) {
                int z = pair2[1];
                composition.add(new int[]{x, z});
            }
        }
    }

    // Convert composition to int[][]
      int[][] result = new int[composition.size()][2];
      for (int i = 0; i < composition.size(); i++) {
        result[i] = composition.get(i);
      }

      return result;
    }


    /*
     * Comprovau si la funció `f` amb domini `dom` i codomini `codom` té inversa. Si la té, retornau
     * el seu graf (el de l'inversa). Sino, retornau null.
     */
    static int[][] exercici5(int[] dom, int[] codom, Function<Integer, Integer> f) {
      int n = dom.length;

    // Create arrays to store function values and inverse mapping
      int[] functionValues = new int[n];
      int[] inverseMapping = new int[n];
      boolean[] codomSet = new boolean[codom.length];

    // Check if f is injective (one-to-one) and fill the functionValues array
      for (int i = 0; i < n; i++) {
        int x = dom[i];
        int y = f.apply(x);

        // Find index of y in codom
        int yIndex = -1;
        for (int j = 0; j < codom.length; j++) {
            if (codom[j] == y) {
                yIndex = j;
                break;
            }
        }
        if (yIndex == -1 || functionValues[yIndex] != 0) {
            return null; // f is not injective or y not in codom
        }

        functionValues[yIndex] = x + 1; // Use x + 1 to avoid default 0 value conflict
    }

    // Check if f is surjective (onto)
      for (int i = 0; i < n; i++) {
        int x = dom[i];
        int y = f.apply(x);

        // Find index of y in codom
        int yIndex = -1;
        for (int j = 0; j < codom.length; j++) {
            if (codom[j] == y) {
                yIndex = j;
                break;
            }
        }
       
        if (yIndex == -1 || codomSet[yIndex]) {
            return null; // f is not surjective or duplicate found
        }

        codomSet[yIndex] = true;
        inverseMapping[yIndex] = x;
    }

    // f is bijective, construct the inverse function graph
      int[][] inverseGraph = new int[n][2];
      int index = 0;
      for (int i = 0; i < codom.length; i++) {
        if (functionValues[i] != 0) {
            inverseGraph[index][0] = codom[i];
            inverseGraph[index][1] = functionValues[i] - 1; // Adjust back to original value
            index++;
        }
      }
      return inverseGraph;
    }


    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // |(a u b) × (a \ c)|

      assertThat(
          exercici1(
            new int[] { 0, 1, 2 },
            new int[] { 1, 2, 3 },
            new int[] { 0, 3 }
          )
          == 8
      );

      assertThat(
          exercici1(
            new int[] { 0, 1 },
            new int[] { 0 },
            new int[] { 0 }
          )
          == 2
      );

      // Exercici 2
      // nombre d'elements de la clausura d'equivalència

      final int[] int08 = { 0, 1, 2, 3, 4, 5, 6, 7, 8 };

      assertThat(exercici2(int08, generateRel(int08, (x, y) -> y == x + 1)) == 81);

      final int[] int123 = { 1, 2, 3 };

      assertThat(exercici2(int123, new int[][] { {1, 3} }) == 5);

      // Exercici 3
      // Si rel és un ordre total, retornar les arestes del diagrama de Hasse

      final int[] int05 = { 0, 1, 2, 3, 4, 5 };

      assertThat(exercici3(int05, generateRel(int05, (x, y) -> x >= y)) == 5);
      assertThat(exercici3(int08, generateRel(int05, (x, y) -> x <= y)) == -2);

      // Exercici 4
      // Composició de grafs de funcions (null si no ho son)

      assertThat(
          exercici4(
            int05,
            generateRel(int05, (x, y) -> x*x == y),
            generateRel(int05, (x, y) -> x == y)
          )
          == null
      );


      var ex4test2 = exercici4(
          int05,
          generateRel(int05, (x, y) -> x + y == 5),
          generateRel(int05, (x, y) -> y == (x + 1) % 6)
        );

      assertThat(
          Arrays.deepEquals(
            lexSorted(ex4test2),
            generateRel(int05, (x, y) -> y == (5 - x + 1) % 6)
          )
      );

      // Exercici 5
      // trobar l'inversa (null si no existeix)

      assertThat(exercici5(int05, int08, x -> x + 3) == null);

      assertThat(
          Arrays.deepEquals(
            lexSorted(exercici5(int08, int08, x -> 8 - x)),
            generateRel(int08, (x, y) -> y == 8 - x)
          )
      );
    }

    /**
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
     */
    static int[][] lexSorted(int[][] arr) {
      if (arr == null) return null;

    // Create a copy of the array to avoid mutating the original array
      int[][] arr2 = Arrays.copyOf(arr, arr.length);

    // Sort using a custom comparator
      Arrays.sort(arr2, (a, b) -> {
        // Compare each element lexicographically
        for (int i = 0; i < Math.min(a.length, b.length); i++) {
            if (a[i] != b[i]) {
                return Integer.compare(a[i], b[i]);
            }
        }
        // If all elements compared so far are equal, the shorter array should come first
        return Integer.compare(a.length, b.length);
      });

      return arr2;
    }


    /**
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
     */
    static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
        ArrayList<int[]> rel = new ArrayList<>();

        for (int a : as) {
            for (int b : bs) {
                if (pred.test(a, b)) {
                    rel.add(new int[] { a, b });
                }
            }
        }

        return rel.toArray(new int[rel.size()][]);
    }

    /// Especialització de generateRel per a = b
    static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
        return generateRel(as, as, pred);
    }

    public static void main(String[] args) {
        int[] dom = {0, 1}; // Placeholder for as
        int[] codom = {0, 1, 2}; // Placeholder for bs
        BiPredicate<Integer, Integer> pred = (a, b) -> a == b;

        // Test generateRel with two different arrays
        int[][] result = generateRel(dom, codom, pred);
        for (int[] pair : result) {
            System.out.println("{" + pair[0] + ", " + pair[1] + "}");
        }

        // Test generateRel with specialization where a = b
        int[][] resultSpecialized = generateRel(dom, pred);
        for (int[] pair : resultSpecialized) {
            System.out.println("{" + pair[0] + ", " + pair[1] + "}");
        }
    }
  }

    static class Tema3 {
      /*
     * Determinau si el graf és connex. Podeu suposar que `g` no és dirigit.
     */
    static boolean exercici1(int[][] g) {
        int n = g.length;
        if (n == 0) {
            return true;
        }

        // Array to track visited nodes
        boolean[] visited = new boolean[n];

        // Start DFS from the first node
        dfs(g, 0, visited);

        // Check if all nodes were visited
        for (boolean v : visited) {
            if (!v) {
                return false;
            }
        }
        return true;
    }

    // Helper method to perform DFS
    static void dfs(int[][] g, int node, boolean[] visited) {
        visited[node] = true;

        for (int neighbor : g[node]) {
            if (!visited[neighbor]) {
                dfs(g, neighbor, visited);
            }
        }
    }

    public static void main(String[] args) {
        // Test cases
        final int[][] B2 = { {}, {} };
        final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };
        final int[][] C3D = { {1}, {2}, {0} };

        System.out.println(exercici1(C3));  // true
        System.out.println(exercici1(B2));  // false
    }

    /*
     * Donat un tauler d'escacs d'amplada `w` i alçada `h`, determinau quin és el mínim nombre de
     * moviments necessaris per moure un cavall de la casella `i` a la casella `j`.
     *
     * Les caselles estan numerades de `0` a `w*h-1` per files. Per exemple, si w=5 i h=2, el tauler
     * és:
     *   0 1 2 3 4
     *   5 6 7 8 9
     *
     * Retornau el nombre mínim de moviments, o -1 si no és possible arribar-hi.
     */
    public class KnightMoves {

    static int[] knightMovesX = {-2, -1, 1, 2, 2, 1, -1, -2};
    static int[] knightMovesY = {1, 2, 2, 1, -1, -2, -2, -1};

    static int exercici2(int w, int h, int i, int j) {
        if (i == j) {
            return 0;
        }

        // Convert linear indices to 2D coordinates
        int startX = i % w;
        int startY = i / w;
        int endX = j % w;
        int endY = j / w;

        boolean[][] visited = new boolean[w][h];
        Queue<int[]> queue = new LinkedList<>();
        queue.add(new int[]{startX, startY, 0}); // {x, y, distance}

        while (!queue.isEmpty()) {
            int[] current = queue.poll();
            int x = current[0];
            int y = current[1];
            int distance = current[2];

            // Try all possible knight moves
            for (int k = 0; k < 8; k++) {
                int newX = x + knightMovesX[k];
                int newY = y + knightMovesY[k];

                if (newX == endX && newY == endY) {
                    return distance + 1;
                }

                if (isValidMove(newX, newY, w, h) && !visited[newX][newY]) {
                    visited[newX][newY] = true;
                    queue.add(new int[]{newX, newY, distance + 1});
                }
            }
        }

        return -1; // If no valid path is found
    }

    static boolean isValidMove(int x, int y, int w, int h) {
        return x >= 0 && y >= 0 && x < w && y < h;
    }

    public static void main(String[] args) {
        // Test cases
        System.out.println(exercici2(4, 3, 0, 11));  // Output: 3
        System.out.println(exercici2(3, 2, 0, 2));   // Output: -1
    }
}

    /*
     * Donat un arbre arrelat (graf dirigit `g`, amb arrel `r`), decidiu si el vèrtex `u` apareix
     * abans (o igual) que el vèrtex `v` al recorregut en preordre de l'arbre.
     */
    static boolean exercici3(int[][] g, int r, int u, int v) {
        List<Integer> preorderList = new ArrayList<>();
        boolean[] visited = new boolean[g.length];
        preorderTraversal(g, r, visited, preorderList);
        
        int indexU = preorderList.indexOf(u);
        int indexV = preorderList.indexOf(v);

        return indexU <= indexV;
    }

    // Helper method to perform preorder traversal
    static void preorderTraversal(int[][] g, int node, boolean[] visited, List<Integer> preorderList) {
        visited[node] = true;
        preorderList.add(node);

        for (int neighbor : g[node]) {
            if (!visited[neighbor]) {
                preorderTraversal(g, neighbor, visited, preorderList);
            }
        }
    }

    public static void main(String[] args) {
        // Example tree
        final int[][] T1 = {
            {1, 2, 3, 4},
            {5},
            {6, 7, 8},
            {},
            {9},
            {},
            {},
            {},
            {},
            {10, 11},
            {},
            {}
        };

        // Test cases
        System.out.println(exercici3(T1, 0, 5, 3));  // Output: true
        System.out.println(exercici3(T1, 0, 6, 2));  // Output: false
    }
}

public class TreeHeight {

    /*
     * Donat un recorregut en preordre (per exemple, el primer vèrtex que hi apareix és `preord[0]`)
     * i el grau de cada vèrtex (per exemple, el vèrtex `i` té grau `d[i]`), trobau l'altura de
     * l'arbre corresponent.
     *
     * L'altura d'un arbre arrelat és la major distància de l'arrel a les fulles.
     */
    static int exercici4(int[] preord, int[] d) {
        if (preord.length == 0) return 0;

        int maxDepth = 0;
        int currentDepth = 0;
        Stack<Integer> stack = new Stack<>();

        for (int i = 0; i < preord.length; i++) {
            while (stack.size() > currentDepth) {
                stack.pop();
            }

            stack.push(preord[i]);
            maxDepth = Math.max(maxDepth, currentDepth);

            currentDepth += d[preord[i]];
            currentDepth = stack.size();
        }

        return maxDepth;
    }

    public static void main(String[] args) {
        // Test cases
        final int[] P1 = {0, 1, 5, 2, 6, 7, 8, 3, 4, 9, 10, 11};
        final int[] D1 = {4, 1, 3, 0, 1, 0, 0, 0, 0, 2, 0, 0};

        final int[] P2 = {0, 1, 2, 3, 4, 5, 6, 7, 8};
        final int[] D2 = {2, 0, 2, 0, 2, 0, 2, 0, 0};

        System.out.println(exercici4(P1, D1));  // Output: 3
        System.out.println(exercici4(P2, D2));  // Output: 4
    }
}

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // G connex?

      final int[][] B2 = { {}, {} };

      final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };

      final int[][] C3D = { {1}, {2}, {0} };

      assertThat(exercici1(C3));
      assertThat(!exercici1(B2));

      // Exercici 2
      // Moviments de cavall

      // Tauler 4x3. Moviments de 0 a 11: 3.
      // 0  1   2   3
      // 4  5   6   7
      // 8  9  10  11
      assertThat(exercici2(4, 3, 0, 11) == 3);

      // Tauler 3x2. Moviments de 0 a 2: (impossible).
      // 0 1 2
      // 3 4 5
      assertThat(exercici2(3, 2, 0, 2) == -1);

      // Exercici 3
      // u apareix abans que v al recorregut en preordre (o u=v)

      final int[][] T1 = {
        {1, 2, 3, 4},
        {5},
        {6, 7, 8},
        {},
        {9},
        {},
        {},
        {},
        {},
        {10, 11},
        {},
        {}
      };

      assertThat(exercici3(T1, 0, 5, 3));
      assertThat(!exercici3(T1, 0, 6, 2));

      // Exercici 4
      // Altura de l'arbre donat el recorregut en preordre

      final int[] P1 = { 0, 1, 5, 2, 6, 7, 8, 3, 4, 9, 10, 11 };
      final int[] D1 = { 4, 1, 3, 0, 1, 0, 0, 0, 0, 2,  0,  0 };

      final int[] P2 = { 0, 1, 2, 3, 4, 5, 6, 7, 8 };
      final int[] D2 = { 2, 0, 2, 0, 2, 0, 2, 0, 0 };

      assertThat(exercici4(P1, D1) == 3);
      assertThat(exercici4(P2, D2) == 4);
    }
  }
  }

  /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
   */
  static class Tema4 {
    /*
     * Calculau el mínim comú múltiple de `a` i `b`.
     */
public class LCMCalculator {

    /*
     * Calculau el mínim comú múltiple de `a` i `b`.
     */
    static int exercici1(int a, int b) {
        return (a / gcd(a, b)) * b;
    }

    // Helper method to calculate the greatest common divisor using the Euclidean algorithm
    static int gcd(int a, int b) {
        while (b != 0) {
            int temp = b;
            b = a % b;
            a = temp;
        }
        return a;
    }

    public static void main(String[] args) {
        // Test cases
        System.out.println(exercici1(12, 18));  // Output: 36
        System.out.println(exercici1(5, 7));    // Output: 35
        System.out.println(exercici1(21, 6));   // Output: 42
        System.out.println(exercici1(0, 5));    // Output: 0
    }
}

public class ModularEquationSolver {

    /*
     * Trobau totes les solucions de l'equació
     *
     *   a·x ≡ b (mod n)
     *
     * donant els seus representants entre 0 i n-1.
     *
     * Podeu suposar que `n > 1`. Recordau que no no podeu utilitzar la força bruta.
     */
    static int[] exercici2(int a, int b, int n) {
        int gcd = gcd(a, n);
        if (b % gcd != 0) {
            return new int[] {}; // No solutions exist
        }

        // Reduce the equation by dividing a, b, and n by gcd
        a /= gcd;
        b /= gcd;
        n /= gcd;

        // Find the particular solution using the extended Euclidean algorithm
        int x0 = modInverse(a, n);
        x0 = (x0 * b) % n;
        if (x0 < 0) {
            x0 += n;
        }

        // All solutions
        int[] solutions = new int[gcd];
        for (int k = 0; k < gcd; k++) {
            solutions[k] = (x0 + k * n) % (n * gcd);
        }

        return solutions;
    }

    // Helper method to calculate the greatest common divisor using the Euclidean algorithm
    static int gcd(int a, int b) {
        while (b != 0) {
            int temp = b;
            b = a % b;
            a = temp;
        }
        return a;
    }

    // Helper method to find the modular inverse using the extended Euclidean algorithm
    static int modInverse(int a, int n) {
        int[] result = extendedGcd(a, n);
        int x = result[0];
        int gcd = result[2];
        if (gcd != 1) {
            throw new IllegalArgumentException("Modular inverse does not exist");
        }
        return x % n;
    }

    // Helper method to perform the extended Euclidean algorithm
    static int[] extendedGcd(int a, int b) {
        if (b == 0) {
            return new int[] {1, 0, a};
        }
        int[] result = extendedGcd(b, a % b);
        int x1 = result[1];
        int y1 = result[0] - (a / b) * result[1];
        return new int[] {x1, y1, result[2]};
    }

    public static void main(String[] args) {
        // Test cases
        System.out.println(Arrays.toString(exercici2(14, 30, 100)));  // Example output: [10, 60]
        System.out.println(Arrays.toString(exercici2(3, 6, 9)));      // Example output: []
        System.out.println(Arrays.toString(exercici2(4, 8, 12)));     // Example output: [2, 5, 8, 11]
    }
}

public class CongruenceSystemSolver {

    /*
     * Donats `a != 0`, `b != 0`, `c`, `d`, `m > 1`, `n > 1`, determinau si el sistema
     *
     *   a·x ≡ c (mod m)
     *   b·x ≡ d (mod n)
     *
     * té solució.
     */
    static boolean exercici3(int a, int b, int c, int d, int m, int n) {
        int gcd1 = gcd(a, m);
        int gcd2 = gcd(b, n);

        // Check if the individual congruences have solutions
        if (c % gcd1 != 0 || d % gcd2 != 0) {
            return false;
        }

        // Reduce the congruences
        a /= gcd1;
        c /= gcd1;
        m /= gcd1;

        b /= gcd2;
        d /= gcd2;
        n /= gcd2;

        // Find a particular solution for each congruence
        int x1 = findParticularSolution(a, c, m);
        int x2 = findParticularSolution(b, d, n);

        // Check if the solutions are compatible using CRT conditions
        int[] result = solveCongruences(x1, m, x2, n);
        return result != null;
    }

    // Helper method to calculate the greatest common divisor using the Euclidean algorithm
    static int gcd(int a, int b) {
        while (b != 0) {
            int temp = b;
            b = a % b;
            a = temp;
        }
        return a;
    }

    // Helper method to find a particular solution to a·x ≡ c (mod m)
    static int findParticularSolution(int a, int c, int m) {
        int[] result = extendedGcd(a, m);
        int x = result[0];
        int gcd = result[2];
        if (gcd != 1) {
            throw new IllegalArgumentException("No solution exists");
        }
        return (x * c) % m;
    }

    // Helper method to perform the extended Euclidean algorithm
    static int[] extendedGcd(int a, int b) {
        if (b == 0) {
            return new int[] {1, 0, a};
        }
        int[] result = extendedGcd(b, a % b);
        int x1 = result[1];
        int y1 = result[0] - (a / b) * result[1];
        return new int[] {x1, y1, result[2]};
    }

    // Helper method to solve two congruences x ≡ a (mod m) and x ≡ b (mod n) using CRT
    static int[] solveCongruences(int a, int m, int b, int n) {
        int[] result = extendedGcd(m, n);
        int gcd = result[2];

        if ((b - a) % gcd != 0) {
            return null;
        }

        int mInverse = result[0];
        int lcm = (m / gcd) * n;
        int x = (a + m * ((b - a) / gcd * mInverse % (n / gcd))) % lcm;

        if (x < 0) {
            x += lcm;
        }

        return new int[] {x, lcm};
    }

    public static void main(String[] args) {
        // Test cases
        System.out.println(exercici3(14, 15, 30, 45, 100, 200)); // Output: true or false depending on compatibility
        System.out.println(exercici3(3, 4, 6, 8, 9, 12));       // Output: true or false depending on compatibility
        System.out.println(exercici3(2, 3, 4, 5, 6, 7));        // Output: true or false depending on compatibility
    }
}

    /*
     * Donats `n` un enter, `k > 0` enter, i `p` un nombre primer, retornau el residu de dividir n^k
     * entre p.
     *
     * Alerta perquè és possible que n^k sigui massa gran com per calcular-lo directament.
     * De fet, assegurau-vos de no utilitzar cap valor superior a max{n, p²}.
     *
     * Anau alerta també abusant de la força bruta, la vostra implementació hauria d'executar-se en
     * qüestió de segons independentment de l'entrada.
     */
static int exercici4(int n, int k, int p) {
    // Funció per calcular la potència modular
    long modPow(long base, int exp, int mod) {
        long result = 1;
        base = base % mod; // Assegurem que la base sigui menor que mod

        while (exp > 0) {
            // Si l'exponent és imparell, multipliquem la base amb el resultat
            if ((exp & 1) == 1) {
                result = (result * base) % mod;
            }
            // L'exponent es divideix per 2
            exp >>= 1;
            // Multipliquem la base amb ella mateixa
            base = (base * base) % mod;
        }
        return result;
    }

    return (int) modPow(n, k, p);
}

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // mcm(a, b)

      assertThat(exercici1(35, 77) == 5*7*11);
      assertThat(exercici1(-8, 12) == 24);

      // Exercici 2
      // Solucions de a·x ≡ b (mod n)

      assertThat(Arrays.equals(exercici2(2, 2, 4), new int[] { 1, 3 }));
      assertThat(Arrays.equals(exercici2(3, 2, 4), new int[] { 2 }));

      // Exercici 3
      // El sistema a·x ≡ c (mod m), b·x ≡ d (mod n) té solució?

      assertThat(exercici3(3, 2, 2, 2, 5, 4));
      assertThat(!exercici3(3, 2, 2, 2, 10, 4));

      // Exercici 4
      // n^k mod p

      assertThat(exercici4(2018, 2018, 5) == 4);
      assertThat(exercici4(-2147483646, 2147483645, 46337) == 7435);
    }
  }

  /**
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `assertThat` per comprovar fàcilment que un valor sigui `true`.
   */
  public static void main(String[] args) {
    Tema1.tests();
    Tema2.tests();
    Tema3.tests();
    Tema4.tests();
  }

  /// Si b és cert, no fa res. Si b és fals, llança una excepció (AssertionError).
  static void assertThat(boolean b) {
    if (!b)
      throw new AssertionError();
  }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
