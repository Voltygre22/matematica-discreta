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
public class Main {
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
  }

  /// Si b és cert, no fa res. Si b és fals, llança una excepció (AssertionError).
  static void assertThat(boolean b) {
    if (!b)
      throw new AssertionError();
  }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
